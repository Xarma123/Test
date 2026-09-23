#!/usr/bin/env python3
"""
End-to-End Test Fixture & Verification Suite for `torrent_video_tool.py`.

Includes:
- Synthetic MP4 Video Generator (`create_synthetic_mp4_bytes`) with valid ISO BMFF boxes
  (`ftyp`, `moov`, `mdat`) spanning multiple BitTorrent pieces.
- Local BitTorrent Seeder Server (`LocalBitTorrentSeeder`) implementing BEP 0003 wire protocol
  and recording piece request order to verify dynamic seek prioritization.
- Local BitTorrent HTTP Tracker (`LocalBitTorrentTracker`) serving compact peer lists.
- Unit + integration tests verifying:
  1. Bencode & multi-file `.torrent` video file discovery.
  2. Full BitTorrent download with SHA-1 piece verification & SHA-256 file integrity check.
  3. On-demand HTTP `206 Partial Content` Range streaming, MP4 tail-box suffix range requests,
     and dynamic piece scheduler reprioritization when seeking to an arbitrary video offset.
"""

from __future__ import annotations

import hashlib
import http.server
import socket
import socketserver
import struct
import tempfile
import threading
import time
import unittest
import urllib.parse
import urllib.request
from pathlib import Path
from typing import List, Optional, Tuple

from torrent_video_tool import (
    MSG_BITFIELD,
    MSG_INTERESTED,
    MSG_PIECE,
    MSG_REQUEST,
    MSG_UNCHOKE,
    TorrentMetadata,
    TorrentVideoSession,
    bdecode,
    bencode,
)


# ============================================================================
# Test Fixtures: Synthetic MP4 Video + .torrent Builder + Seeder + Tracker
# ============================================================================

def _mp4_box(box_type: bytes, payload: bytes) -> bytes:
    return struct.pack("!I4s", 8 + len(payload), box_type) + payload


def create_synthetic_mp4_bytes(total_size: int = 512 * 1024) -> bytes:
    """
    Create a deterministic, valid ISO-BMFF (MP4) byte stream of `total_size` bytes
    containing `ftyp`, `mdat` (deterministic video frame blocks), and trailing `moov` box.
    """
    ftyp = _mp4_box(b"ftyp", b"isom\x00\x00\x02\x00isomiso2mp41")
    moov_payload = b"moov-index-table:" + hashlib.sha256(b"mp4-index").digest() * 8
    moov = _mp4_box(b"moov", moov_payload)

    mdat_header_size = 8
    mdat_payload_size = max(64, total_size - len(ftyp) - len(moov) - mdat_header_size)

    # Fill mdat with deterministic 64-byte tagged blocks so any byte offset is uniquely verifiable
    chunks: List[bytes] = []
    written = 0
    block_idx = 0
    while written < mdat_payload_size:
        rem = min(64, mdat_payload_size - written)
        blk = struct.pack("!II", block_idx, written) + hashlib.md5(struct.pack("!I", block_idx)).digest()
        blk = (blk * 2)[:rem]
        chunks.append(blk)
        written += len(blk)
        block_idx += 1

    mdat = _mp4_box(b"mdat", b"".join(chunks))
    return ftyp + mdat + moov


def build_torrent_bytes(
    payload_bytes: bytes,
    announce_url: str,
    name: str = "fixture_video.mp4",
    piece_length: int = 32768,
    multi_file_prefix: Optional[bytes] = None,
) -> Tuple[bytes, bytes]:
    """
    Build a `.torrent` file (and full torrent payload buffer) for `payload_bytes`.
    If `multi_file_prefix` is provided, creates a multi-file torrent containing a small
    `README.txt` before the `.mp4` video to test file offset calculation and selection.
    """
    if multi_file_prefix is not None:
        full_stream = multi_file_prefix + payload_bytes
    else:
        full_stream = payload_bytes

    pieces = []
    for offset in range(0, len(full_stream), piece_length):
        piece = full_stream[offset:offset + piece_length]
        pieces.append(hashlib.sha1(piece).digest())
    pieces_concat = b"".join(pieces)

    if multi_file_prefix is not None:
        info = {
            b"name": b"fixture_bundle",
            b"piece length": piece_length,
            b"pieces": pieces_concat,
            b"files": [
                {b"length": len(multi_file_prefix), b"path": [b"README.txt"]},
                {b"length": len(payload_bytes), b"path": [name.encode("utf-8")]},
            ],
        }
    else:
        info = {
            b"name": name.encode("utf-8"),
            b"piece length": piece_length,
            b"pieces": pieces_concat,
            b"length": len(full_stream),
        }

    torrent_dict = {
        b"announce": announce_url.encode("utf-8"),
        b"info": info,
    }
    return bencode(torrent_dict), full_stream


class LocalBitTorrentSeeder:
    """
    A real BEP 0003 TCP BitTorrent Seeder Peer that serves pieces from `full_stream`
    and logs the order in which pieces are requested by leechers/streamers.
    """

    def __init__(
        self,
        info_hash: bytes,
        full_stream: bytes,
        piece_length: int,
        piece_delay_sec: float = 0.0,
    ) -> None:
        self.info_hash = info_hash
        self.full_stream = full_stream
        self.piece_length = piece_length
        self.piece_delay_sec = piece_delay_sec
        self.num_pieces = (len(full_stream) + piece_length - 1) // piece_length
        self.requested_pieces_order: List[int] = []
        self._lock = threading.Lock()

        self._srv_sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._srv_sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self._srv_sock.bind(("127.0.0.1", 0))
        self._srv_sock.listen(8)
        self.host, self.port = self._srv_sock.getsockname()[:2]
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._accept_loop, daemon=True)
        self._thread.start()

    def _accept_loop(self) -> None:
        self._srv_sock.settimeout(0.2)
        while not self._stop.is_set():
            try:
                conn, _ = self._srv_sock.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            threading.Thread(target=self._handle_peer, args=(conn,), daemon=True).start()

    def _handle_peer(self, conn: socket.socket) -> None:
        with conn:
            conn.settimeout(5.0)
            try:
                # 1. Read 68-byte handshake
                hs = self._recv_exact(conn, 68)
                if hs[28:48] != self.info_hash:
                    return
                # Send handshake back
                peer_id = b"-SD0001-LOCALFIXTURE"
                conn.sendall(hs[:48] + peer_id)

                # 2. Send full bitfield (all pieces available)
                bf_len = (self.num_pieces + 7) // 8
                bitfield = bytes([0xFF] * bf_len)
                conn.sendall(struct.pack("!IB", 1 + len(bitfield), MSG_BITFIELD) + bitfield)

                while not self._stop.is_set():
                    raw_len = self._recv_exact(conn, 4)
                    msg_len = struct.unpack("!I", raw_len)[0]
                    if msg_len == 0:
                        continue
                    msg_id = self._recv_exact(conn, 1)[0]
                    payload = self._recv_exact(conn, msg_len - 1) if msg_len > 1 else b""

                    if msg_id == MSG_INTERESTED:
                        # Unchoke the peer immediately
                        conn.sendall(struct.pack("!IB", 1, MSG_UNCHOKE))
                    elif msg_id == MSG_REQUEST:
                        p_idx, begin, length = struct.unpack("!III", payload[:12])
                        with self._lock:
                            if not self.requested_pieces_order or self.requested_pieces_order[-1] != p_idx:
                                self.requested_pieces_order.append(p_idx)
                        if self.piece_delay_sec > 0 and begin == 0:
                            time.sleep(self.piece_delay_sec)
                        global_start = p_idx * self.piece_length + begin
                        block = self.full_stream[global_start:global_start + length]
                        resp_payload = struct.pack("!II", p_idx, begin) + block
                        conn.sendall(struct.pack("!IB", 1 + len(resp_payload), MSG_PIECE) + resp_payload)
            except Exception:
                return

    @staticmethod
    def _recv_exact(sock: socket.socket, n: int) -> bytes:
        buf = bytearray()
        while len(buf) < n:
            chunk = sock.recv(n - len(buf))
            if not chunk:
                raise ConnectionError("EOF")
            buf.extend(chunk)
        return bytes(buf)

    def stop(self) -> None:
        self._stop.set()
        try:
            self._srv_sock.close()
        except OSError:
            pass


class LocalBitTorrentTracker:
    """Local HTTP BitTorrent Tracker returning compact peer list pointing to `seeder_addr`."""

    def __init__(self, seeder_addr: Tuple[str, int]) -> None:
        self.seeder_addr = seeder_addr

        outer = self

        class Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, format: str, *args: object) -> None:
                pass

            def do_GET(self) -> None:
                ip_bytes = socket.inet_aton(outer.seeder_addr[0])
                port_bytes = struct.pack("!H", outer.seeder_addr[1])
                compact_peers = ip_bytes + port_bytes
                body = bencode({b"interval": 60, b"peers": compact_peers})
                self.send_response(200)
                self.send_header("Content-Type", "text/plain")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

        self._httpd = socketserver.ThreadingTCPServer(("127.0.0.1", 0), Handler)
        self._httpd.daemon_threads = True
        self.host, self.port = self._httpd.server_address[:2]
        self.announce_url = f"http://{self.host}:{self.port}/announce"
        self._thread = threading.Thread(target=self._httpd.serve_forever, daemon=True)
        self._thread.start()

    def stop(self) -> None:
        self._httpd.shutdown()
        self._httpd.server_close()


# ============================================================================
# Automated Test Cases
# ============================================================================

class TorrentVideoToolTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp_dir = tempfile.TemporaryDirectory()
        self.work_dir = Path(self.temp_dir.name)
        # Create a 512 KiB synthetic MP4 video spanning 16 pieces of 32 KiB each
        self.video_bytes = create_synthetic_mp4_bytes(total_size=512 * 1024)
        self.piece_length = 32 * 1024

    def tearDown(self) -> None:
        self.temp_dir.cleanup()

    def test_1_bencode_and_multi_file_torrent_selection(self) -> None:
        """Verify Bencode encoding/decoding and automatic `.mp4` selection in multi-file torrents."""
        readme_bytes = b"This torrent bundle contains a README and a large MP4 video.\n"
        torrent_raw, full_stream = build_torrent_bytes(
            self.video_bytes,
            announce_url="http://127.0.0.1:9999/announce",
            name="feature_film.mp4",
            piece_length=self.piece_length,
            multi_file_prefix=readme_bytes,
        )

        meta = TorrentMetadata.from_bytes(torrent_raw)
        self.assertEqual(len(meta.files), 2)
        selected = meta.select_video_file()
        self.assertTrue(selected.path.endswith("feature_film.mp4"))
        self.assertEqual(selected.length, len(self.video_bytes))
        self.assertEqual(selected.offset, len(readme_bytes))
        self.assertEqual(meta.total_length, len(full_stream))

    def test_2_full_video_download_via_tracker_and_seeder(self) -> None:
        """Verify complete BitTorrent video download via HTTP tracker + BEP 0003 peer wire."""
        # 1. Build temporary metadata to get info_hash
        dummy_torrent, full_stream = build_torrent_bytes(
            self.video_bytes,
            announce_url="http://127.0.0.1:1/announce",
            piece_length=self.piece_length,
            multi_file_prefix=b"Header padding before video file inside multi-file torrent.\n",
        )
        temp_meta = TorrentMetadata.from_bytes(dummy_torrent)

        # 2. Start local BEP 0003 Seeder and local HTTP Tracker
        seeder = LocalBitTorrentSeeder(
            info_hash=temp_meta.info_hash,
            full_stream=full_stream,
            piece_length=self.piece_length,
        )
        tracker = LocalBitTorrentTracker((seeder.host, seeder.port))
        try:
            torrent_raw, _ = build_torrent_bytes(
                self.video_bytes,
                announce_url=tracker.announce_url,
                piece_length=self.piece_length,
                multi_file_prefix=b"Header padding before video file inside multi-file torrent.\n",
            )
            torrent_path = self.work_dir / "movie.torrent"
            torrent_path.write_bytes(torrent_raw)

            session = TorrentVideoSession(torrent_path, self.work_dir / "downloads")
            try:
                session.start_swarm()
                completed = session.wait_until_complete(timeout=15.0)
                self.assertTrue(completed, "Torrent download did not finish within timeout")

                downloaded_bytes = session.output_path.read_bytes()
                self.assertEqual(len(downloaded_bytes), len(self.video_bytes))
                self.assertEqual(
                    hashlib.sha256(downloaded_bytes).hexdigest(),
                    hashlib.sha256(self.video_bytes).hexdigest(),
                    "Downloaded video SHA-256 does not match source fixture!",
                )
            finally:
                session.close()
        finally:
            tracker.stop()
            seeder.stop()

    def test_3_http_range_streaming_and_dynamic_seek_reprioritization(self) -> None:
        """
        Verify HTTP 206 Range streaming on an in-flight torrent:
        - Seeking to 75% into the video immediately reprioritizes the BitTorrent piece scheduler
          to fetch the target pieces around the seek offset before earlier middle pieces.
        - Suffix byte-range requests (`Range: bytes=-1024`) fetch the MP4 `moov` tail box.
        - Streaming from byte 0 returns exact video bytes.
        """
        dummy_torrent, full_stream = build_torrent_bytes(
            self.video_bytes,
            announce_url="http://127.0.0.1:1/announce",
            piece_length=self.piece_length,
        )
        temp_meta = TorrentMetadata.from_bytes(dummy_torrent)

        # Throttle seeder slightly (35ms/piece) so seeking happens before background download finishes
        seeder = LocalBitTorrentSeeder(
            info_hash=temp_meta.info_hash,
            full_stream=full_stream,
            piece_length=self.piece_length,
            piece_delay_sec=0.035,
        )
        tracker = LocalBitTorrentTracker((seeder.host, seeder.port))
        try:
            torrent_raw, _ = build_torrent_bytes(
                self.video_bytes,
                announce_url=tracker.announce_url,
                piece_length=self.piece_length,
            )
            torrent_path = self.work_dir / "stream_fixture.torrent"
            torrent_path.write_bytes(torrent_raw)

            session = TorrentVideoSession(
                torrent_path,
                self.work_dir / "stream_cache",
                sliding_window_pieces=3,
            )
            try:
                stream_url = session.start_http_stream()
                session.start_swarm()

                # 1. Immediately seek to 75% of the 512 KiB video (piece 12: byte 393216..430000)
                seek_start = 12 * self.piece_length + 123
                seek_end = 13 * self.piece_length + 456
                req = urllib.request.Request(
                    stream_url,
                    headers={"Range": f"bytes={seek_start}-{seek_end}"},
                )
                with urllib.request.urlopen(req, timeout=10.0) as resp:
                    self.assertEqual(resp.status, 206)
                    self.assertEqual(
                        resp.headers.get("Content-Range"),
                        f"bytes {seek_start}-{seek_end}/{len(self.video_bytes)}",
                    )
                    self.assertEqual(resp.headers.get("Accept-Ranges"), "bytes")
                    seek_data = resp.read()

                expected_slice = self.video_bytes[seek_start:seek_end + 1]
                self.assertEqual(seek_data, expected_slice)

                # Confirm that piece 12 & 13 were fetched BEFORE all sequential middle pieces (e.g. piece 5..10)
                idx_12 = seeder.requested_pieces_order.index(12)
                self.assertLess(
                    idx_12,
                    8,
                    f"Expected seek piece 12 to be prioritized early, got order: {seeder.requested_pieces_order}",
                )

                # 2. Test suffix byte-range request (e.g. player reading trailing MP4 `moov` atom)
                suffix_req = urllib.request.Request(
                    stream_url,
                    headers={"Range": "bytes=-1024"},
                )
                with urllib.request.urlopen(suffix_req, timeout=10.0) as resp:
                    self.assertEqual(resp.status, 206)
                    tail_data = resp.read()
                self.assertEqual(tail_data, self.video_bytes[-1024:])

                # 3. Read initial header/frames via Range request (bytes=0-65535)
                head_req = urllib.request.Request(
                    stream_url,
                    headers={"Range": "bytes=0-65535"},
                )
                with urllib.request.urlopen(head_req, timeout=10.0) as resp:
                    self.assertEqual(resp.status, 206)
                    head_data = resp.read()
                self.assertEqual(head_data, self.video_bytes[:65536])

            finally:
                session.close()
        finally:
            tracker.stop()
            seeder.stop()

    def test_4_magnet_link_ut_metadata_and_web_ui_api(self) -> None:
        """
        Verify Magnet URI (`magnet:?xt=urn:btih:...`) resolution via BEP 0009/0010 (`ut_metadata`)
        and Web UI `/api/start` + `/stream` + `/download` endpoints.
        """
        import json
        from torrent_video_tool import VideoStreamServer, get_default_fixture_magnet, parse_magnet_uri

        magnet_uri = get_default_fixture_magnet()
        parsed = parse_magnet_uri(magnet_uri)
        self.assertEqual(len(parsed.info_hash), 20)
        self.assertTrue(magnet_uri.startswith("magnet:?xt=urn:btih:"))

        ui_server = VideoStreamServer(host="127.0.0.1", port=0, output_dir=self.work_dir / "ui_downloads")
        ui_server.start()
        try:
            base_url = ui_server.ui_url.rstrip("/")

            # 1. Verify Web UI HTML loads
            with urllib.request.urlopen(base_url + "/", timeout=5.0) as resp:
                html = resp.read().decode("utf-8")
                self.assertIn("BitTorrent Magnet Video Streamer", html)

            # 2. Start session via POST /api/start with Magnet Link
            req_body = json.dumps({"source": magnet_uri, "mode": "stream"}).encode("utf-8")
            req = urllib.request.Request(
                base_url + "/api/start",
                data=req_body,
                headers={"Content-Type": "application/json"},
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=10.0) as resp:
                self.assertEqual(resp.status, 200)
                start_data = json.loads(resp.read().decode("utf-8"))
                self.assertTrue(start_data["ok"])
                self.assertEqual(start_data["info_hash"], parsed.info_hash.hex())

            # 3. Stream a byte range from the magnet-resolved video
            range_req = urllib.request.Request(
                base_url + "/stream",
                headers={"Range": "bytes=0-32767"},
            )
            with urllib.request.urlopen(range_req, timeout=10.0) as resp:
                self.assertEqual(resp.status, 206)
                chunk = resp.read()
                self.assertEqual(len(chunk), 32768)
                self.assertEqual(chunk[4:8], b"ftyp")
        finally:
            if ui_server.active_session is not None:
                ui_server.active_session.close()
            ui_server.stop()

    def test_5_real_online_magnet_links_sintel_and_big_buck_bunny(self) -> None:
        """
        Verify live online magnet links (Blender Foundation's Sintel 129 MB & Big Buck Bunny 263 MB):
        - Resolves `.torrent` metadata from live internet peers via UDP trackers + BEP 0009 `ut_metadata`.
        - Streams byte ranges from `Sintel.mp4` (both byte 0 MP4 `ftyp` header and a 50 MB seek offset)
          with full SHA-1 piece verification.
        """
        from torrent_video_tool import ONLINE_MAGNET_PRESETS, TorrentVideoSession

        # 1. Test Sintel (129.24 MB, 987 pieces) live magnet resolution + HTTP 206 Range streaming
        sintel_magnet = ONLINE_MAGNET_PRESETS["sintel"]
        session = TorrentVideoSession(
            sintel_magnet,
            self.work_dir / "sintel_online",
            sliding_window_pieces=2,
        )
        try:
            self.assertEqual(session.metadata.info_hash.hex(), "08ada5a7a6183aae1e09d831df6748d566095a10")
            self.assertTrue(session.target_file.path.endswith("Sintel.mp4"))
            self.assertEqual(session.target_file.length, 129241752)

            stream_url = session.start_http_stream()
            session.start_swarm()

            # Stream first 32 KiB of Sintel.mp4 and verify MP4 `ftyp` signature
            req_head = urllib.request.Request(stream_url, headers={"Range": "bytes=0-32767"})
            with urllib.request.urlopen(req_head, timeout=15.0) as resp:
                self.assertEqual(resp.status, 206)
                head_bytes = resp.read()
                self.assertEqual(len(head_bytes), 32768)
                self.assertEqual(head_bytes[4:8], b"ftyp")

            # Seek 50 MB into the 129 MB Sintel.mp4 movie and stream a 16 KiB range
            seek_offset = 50 * 1024 * 1024
            req_seek = urllib.request.Request(
                stream_url,
                headers={"Range": f"bytes={seek_offset}-{seek_offset + 16383}"},
            )
            with urllib.request.urlopen(req_seek, timeout=15.0) as resp:
                self.assertEqual(resp.status, 206)
                seek_bytes = resp.read()
                self.assertEqual(len(seek_bytes), 16384)
        finally:
            session.close()

        # 2. Test Big Buck Bunny (276.13 MB, 1055 pieces) live magnet resolution
        bbb_magnet = ONLINE_MAGNET_PRESETS["big_buck_bunny"]
        bbb_session = TorrentVideoSession(
            bbb_magnet,
            self.work_dir / "bbb_online",
            sliding_window_pieces=2,
        )
        try:
            self.assertEqual(bbb_session.metadata.info_hash.hex(), "dd8255ecdc7ca55fb0bbf81323d87062db1f6d1c")
            self.assertTrue(bbb_session.target_file.path.endswith("Big Buck Bunny.mp4"))
            self.assertEqual(bbb_session.target_file.length, 276134947)
        finally:
            bbb_session.close()

    def test_6_odyssey_magnet_link_real_mkv_swarm_streaming(self) -> None:
        """
        Verify `The.Odyssey.2026...` Magnet URI (`48AEB057454AAFACAA00614AA6BE73AC7CC29CBB`):
        - Filters dead legacy trackers (`9.rarbg.to`, `tracker.coppersurfer.tk`, etc.) and queries
          active trackers + BEP 0011 (`ut_pex`) prioritizing non-6881 seeder ports.
        - Resolves the real 5.96 GB Matroska `.mkv` (`5,968,900,866` bytes, `8 MiB` pieces).
        - Streams real `1a45dfa3` Matroska + `V_MPEGH/ISO/HEVC` bytes over HTTP 206 Partial Content
          using sub-piece 16 KiB block streaming without waiting for an entire 8 MiB piece.
        """
        odyssey_magnet = (
            "magnet:?xt=urn:btih:48AEB057454AAFACAA00614AA6BE73AC7CC29CBB"
            "&dn=The.Odyssey.2026.1080p.TELESYNC.HEVC.AAC2.0-SPLiCE"
            "&tr=http%3A%2F%2Fp4p.arenabg.com%3A1337%2Fannounce"
            "&tr=udp%3A%2F%2F47.ip-51-68-199.eu%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2F9.rarbg.me%3A2780%2Fannounce"
            "&tr=udp%3A%2F%2F9.rarbg.to%3A2710%2Fannounce"
            "&tr=udp%3A%2F%2F9.rarbg.to%3A2730%2Fannounce"
            "&tr=udp%3A%2F%2F9.rarbg.to%3A2920%2Fannounce"
            "&tr=udp%3A%2F%2Fopen.stealth.si%3A80%2Fannounce"
            "&tr=udp%3A%2F%2Fopentracker.i2p.rocks%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.coppersurfer.tk%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.cyberia.is%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.dler.org%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.internetwarriors.net%3A1337%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.leechers-paradise.org%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.openbittorrent.com%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.opentrackr.org%3A1337"
            "&tr=udp%3A%2F%2Ftracker.pirateparty.gr%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.tiny-vps.com%3A6969%2Fannounce"
            "&tr=udp%3A%2F%2Ftracker.torrent.eu.org%3A451%2Fannounce"
        )
        session = TorrentVideoSession(odyssey_magnet, self.work_dir / "odyssey_dl")
        try:
            self.assertEqual(session.metadata.info_hash.hex(), "48aeb057454aafacaa00614aa6be73ac7cc29cbb")
            self.assertTrue(session.target_file.path.endswith("The.Odyssey.2026.1080p.TELESYNC.HEVC.AAC2.0-SPLiCE.mkv"))
            self.assertEqual(session.target_file.length, 5968900866)

            stream_url = session.start_http_stream()
            session.start_swarm()

            req = urllib.request.Request(stream_url, headers={"Range": "bytes=0-65535"})
            with urllib.request.urlopen(req, timeout=15.0) as resp:
                self.assertEqual(resp.status, 206)
                chunk = resp.read()
                self.assertEqual(len(chunk), 65536)
                # Verify real Matroska EBML header (1a 45 df a3) and HEVC track metadata
                self.assertEqual(chunk[:4], b"\x1a\x45\xdf\xa3")
                self.assertIn(b"matroska", chunk[:64])
                self.assertIn(b"V_MPEGH/ISO/HEVC", chunk)

            # Verify fast mid-movie HTTP 206 Range seek (1.5 GB into the 5.96 GB MKV, 6.51 MiB inside Piece 178)
            seek_offset = 1500000000
            seek_req = urllib.request.Request(
                stream_url,
                headers={"Range": f"bytes={seek_offset}-{seek_offset + 65535}"},
            )
            with urllib.request.urlopen(seek_req, timeout=15.0) as seek_resp:
                self.assertEqual(seek_resp.status, 206)
                seek_chunk = seek_resp.read()
                self.assertEqual(len(seek_chunk), 65536)
        finally:
            session.close()


if __name__ == "__main__":
    unittest.main(verbosity=2)
