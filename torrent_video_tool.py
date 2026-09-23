#!/usr/bin/env python3
"""
Torrent & Magnet Video Downloader + HTTP Range Streamer + Interactive Web UI

Capabilities:
- Pure Python 3 implementation of:
  - Bencode (BEP 0003)
  - Magnet URI parser (`magnet:?xt=urn:btih:...`) with Hex & Base32 info_hash support
  - BEP 0010 Extension Protocol & BEP 0009 (`ut_metadata`) for resolving `.torrent` metadata
    directly from peers using only a magnet link
  - HTTP/HTTPS Tracker Client & UDP Tracker Client (BEP 0015)
  - BitTorrent Peer Wire Protocol (BEP 0003) with 16 KiB pipelined block requests
- Arbitrary-size video support via sparse disk-backed piece storage (`pread`/`pwrite`)
  and dynamic seek-ahead piece prioritization (`HTTP 206 Partial Content`).
- Built-in Web UI (`http://127.0.0.1:8080`) where users can paste a Magnet Link (or load
  the built-in playable H.264 MP4 test fixture magnet link) and click **Stream** or **Download**.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import http.server
import json
import os
import random
import socket
import socketserver
import struct
import sys
import threading
import time
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple


# ============================================================================
# 1. Bencode Encoder / Decoder (BEP 0003)
# ============================================================================

class BencodeError(ValueError):
    """Raised when bencoded data is malformed."""


def bdecode(data: bytes) -> Any:
    """Decode bencoded bytes into Python structures (bytes, int, list, dict)."""
    val, idx = _bdecode_at(data, 0)
    if idx != len(data):
        raise BencodeError(f"Trailing data at byte {idx}")
    return val


def bdecode_prefix(data: bytes) -> Tuple[Any, bytes]:
    """Decode the first bencoded value from `data` and return `(value, remaining_bytes)`."""
    val, idx = _bdecode_at(data, 0)
    return val, data[idx:]


def _bdecode_at(data: bytes, idx: int) -> Tuple[Any, int]:
    if idx >= len(data):
        raise BencodeError("Unexpected EOF in bencoded data")

    ch = data[idx:idx + 1]
    if ch == b"i":
        end = data.find(b"e", idx + 1)
        if end == -1:
            raise BencodeError("Unterminated integer")
        num_bytes = data[idx + 1:end]
        if (num_bytes.startswith(b"0") and len(num_bytes) > 1) or num_bytes == b"-0":
            raise BencodeError("Invalid leading zero in integer")
        return int(num_bytes), end + 1

    if ch == b"l":
        idx += 1
        items = []
        while data[idx:idx + 1] != b"e":
            item, idx = _bdecode_at(data, idx)
            items.append(item)
        return items, idx + 1

    if ch == b"d":
        idx += 1
        mapping: Dict[bytes, Any] = {}
        while data[idx:idx + 1] != b"e":
            key, idx = _bdecode_at(data, idx)
            if not isinstance(key, bytes):
                raise BencodeError("Dictionary keys must be byte strings")
            val, idx = _bdecode_at(data, idx)
            mapping[key] = val
        return mapping, idx + 1

    if b"0" <= ch <= b"9":
        colon = data.find(b":", idx)
        if colon == -1:
            raise BencodeError("Missing colon in byte string length")
        length = int(data[idx:colon])
        start = colon + 1
        end = start + length
        if end > len(data):
            raise BencodeError("Byte string truncated")
        return data[start:end], end

    raise BencodeError(f"Invalid bencode prefix {ch!r} at index {idx}")


def bencode(obj: Any) -> bytes:
    """Encode Python object (int, bytes, str, list, dict) into bencoded bytes."""
    if isinstance(obj, bool):
        return b"i1e" if obj else b"i0e"
    if isinstance(obj, int):
        return f"i{obj}e".encode("ascii")
    if isinstance(obj, bytes):
        return f"{len(obj)}:".encode("ascii") + obj
    if isinstance(obj, str):
        raw = obj.encode("utf-8")
        return f"{len(raw)}:".encode("ascii") + raw
    if isinstance(obj, (list, tuple)):
        return b"l" + b"".join(bencode(x) for x in obj) + b"e"
    if isinstance(obj, dict):
        encoded_items: List[Tuple[bytes, bytes]] = []
        for k, v in obj.items():
            kb = k if isinstance(k, bytes) else str(k).encode("utf-8")
            encoded_items.append((kb, bencode(v)))
        encoded_items.sort(key=lambda pair: pair[0])
        out = [b"d"]
        for kb, vb in encoded_items:
            out.append(bencode(kb))
            out.append(vb)
        out.append(b"e")
        return b"".join(out)
    raise TypeError(f"Unsupported type for bencode: {type(obj)}")


# ============================================================================
# 2. Magnet Link Parser & Torrent Metadata (BEP 0003 + BEP 0009)
# ============================================================================

VIDEO_EXTENSIONS = {".mp4", ".mkv", ".webm", ".avi", ".mov", ".m4v", ".ts", ".ogv"}


@dataclass
class MagnetInfo:
    info_hash: bytes
    display_name: str
    trackers: List[str]
    explicit_peers: List[Tuple[str, int]]
    raw_uri: str


def parse_magnet_uri(uri: str) -> MagnetInfo:
    """
    Parse a `magnet:?xt=urn:btih:<hash>&dn=...&tr=...&x.pe=host:port` link.
    Supports both 40-char hex SHA-1 info hashes and 32-char Base32 info hashes.
    """
    uri = uri.strip()
    if not uri.startswith("magnet:?"):
        raise ValueError(f"Invalid magnet URI (must start with 'magnet:?'): {uri}")

    parsed = urllib.parse.urlsplit(uri)
    qs = urllib.parse.parse_qs(parsed.query)

    xt_list = qs.get("xt", [])
    info_hash: Optional[bytes] = None
    for xt in xt_list:
        if xt.lower().startswith("urn:btih:"):
            hash_str = xt[9:].strip()
            if len(hash_str) == 40:
                info_hash = bytes.fromhex(hash_str)
                break
            elif len(hash_str) == 32:
                info_hash = base64.b32decode(hash_str.upper())
                break

    if info_hash is None or len(info_hash) != 20:
        raise ValueError("Magnet URI missing valid 20-byte SHA-1 'xt=urn:btih:' info_hash")

    display_name = qs.get("dn", ["magnet_video.mp4"])[0]
    trackers = list(dict.fromkeys(qs.get("tr", [])))

    explicit_peers: List[Tuple[str, int]] = []
    for pe in qs.get("x.pe", []) + qs.get("peer", []):
        host, _, port_str = pe.rpartition(":")
        if host and port_str.isdigit():
            explicit_peers.append((host, int(port_str)))

    return MagnetInfo(
        info_hash=info_hash,
        display_name=display_name,
        trackers=trackers,
        explicit_peers=explicit_peers,
        raw_uri=uri,
    )


@dataclass
class TorrentFileEntry:
    path: str
    length: int
    offset: int


@dataclass
class TorrentMetadata:
    announce: str
    announce_list: List[str]
    info_hash: bytes
    name: str
    piece_length: int
    piece_hashes: List[bytes]
    total_length: int
    files: List[TorrentFileEntry]
    raw_info_bytes: bytes = b""

    @property
    def num_pieces(self) -> int:
        return len(self.piece_hashes)

    def piece_size(self, piece_index: int) -> int:
        if piece_index < 0 or piece_index >= self.num_pieces:
            raise IndexError(f"Piece index {piece_index} out of range")
        if piece_index == self.num_pieces - 1:
            rem = self.total_length % self.piece_length
            return rem if rem != 0 else self.piece_length
        return self.piece_length

    def select_video_file(self, preferred_index: Optional[int] = None) -> TorrentFileEntry:
        if preferred_index is not None:
            return self.files[preferred_index]
        video_candidates = [
            f for f in self.files if Path(f.path).suffix.lower() in VIDEO_EXTENSIONS
        ]
        if video_candidates:
            return max(video_candidates, key=lambda f: f.length)
        return max(self.files, key=lambda f: f.length)

    def to_magnet_uri(self, extra_peers: Optional[List[Tuple[str, int]]] = None) -> str:
        params: List[Tuple[str, str]] = [
            ("xt", f"urn:btih:{self.info_hash.hex()}"),
            ("dn", self.name),
        ]
        for tr in self.announce_list:
            if tr:
                params.append(("tr", tr))
        if extra_peers:
            for host, port in extra_peers:
                params.append(("x.pe", f"{host}:{port}"))
        query = "&".join(
            f"{k}={urllib.parse.quote(v, safe=':/')}" for k, v in params
        )
        return f"magnet:?{query}"

    @classmethod
    def from_file(cls, torrent_path: str | Path) -> "TorrentMetadata":
        return cls.from_bytes(Path(torrent_path).read_bytes())

    @classmethod
    def from_bytes(cls, raw: bytes) -> "TorrentMetadata":
        meta = bdecode(raw)
        if not isinstance(meta, dict) or b"info" not in meta:
            raise ValueError("Invalid .torrent file: missing 'info' dictionary")

        announce = meta.get(b"announce", b"").decode("utf-8", errors="replace")
        announce_list: List[str] = [announce] if announce else []
        if b"announce-list" in meta and isinstance(meta[b"announce-list"], list):
            for tier in meta[b"announce-list"]:
                if isinstance(tier, list):
                    for tr in tier:
                        if isinstance(tr, bytes):
                            tr_s = tr.decode("utf-8", errors="replace")
                            if tr_s not in announce_list:
                                announce_list.append(tr_s)

        return cls.from_info_dict(meta[b"info"], announce=announce, announce_list=announce_list)

    @classmethod
    def from_info_dict(
        cls,
        info: Dict[bytes, Any],
        announce: str = "",
        announce_list: Optional[List[str]] = None,
    ) -> "TorrentMetadata":
        info_bencoded = bencode(info)
        info_hash = hashlib.sha1(info_bencoded).digest()
        name = info.get(b"name", b"video.mp4").decode("utf-8", errors="replace")
        piece_length = int(info[b"piece length"])
        pieces_blob = info[b"pieces"]
        if len(pieces_blob) % 20 != 0:
            raise ValueError("Invalid .torrent pieces length (not a multiple of 20)")
        piece_hashes = [
            pieces_blob[i:i + 20] for i in range(0, len(pieces_blob), 20)
        ]

        files: List[TorrentFileEntry] = []
        offset = 0
        if b"files" in info:
            for fdict in info[b"files"]:
                flen = int(fdict[b"length"])
                parts = [p.decode("utf-8", errors="replace") for p in fdict[b"path"]]
                rel_path = os.path.join(name, *parts)
                files.append(TorrentFileEntry(path=rel_path, length=flen, offset=offset))
                offset += flen
            total_length = offset
        else:
            total_length = int(info[b"length"])
            files.append(TorrentFileEntry(path=name, length=total_length, offset=0))

        return cls(
            announce=announce,
            announce_list=announce_list or ([announce] if announce else []),
            info_hash=info_hash,
            name=name,
            piece_length=piece_length,
            piece_hashes=piece_hashes,
            total_length=total_length,
            files=files,
            raw_info_bytes=info_bencoded,
        )


# ============================================================================
# 3. Sparse Disk-Backed Piece Store & Priority Scheduler (Any Video Size)
# ============================================================================

class SparseVideoPieceStore:
    """
    Manages piece storage and prioritization for arbitrary-size videos.
    Writes verified pieces directly to their exact byte offsets on disk via `pwrite`
    so memory stays bounded to O(active_pieces * piece_length).
    """

    def __init__(
        self,
        metadata: TorrentMetadata,
        target_file: TorrentFileEntry,
        output_path: str | Path,
        sliding_window_pieces: int = 8,
    ) -> None:
        self.metadata = metadata
        self.target_file = target_file
        self.output_path = Path(output_path)
        self.sliding_window_pieces = max(2, sliding_window_pieces)

        self.first_piece = target_file.offset // metadata.piece_length
        end_byte = max(target_file.offset, target_file.offset + target_file.length - 1)
        self.last_piece = end_byte // metadata.piece_length if target_file.length > 0 else 0
        self.required_pieces: Set[int] = set(range(self.first_piece, self.last_piece + 1))

        self._lock = threading.Condition()
        self.completed_pieces: Set[int] = set()
        self.in_progress_pieces: Set[int] = set()
        self._priority_cursor: int = self.first_piece
        self._urgent_pieces: List[int] = []
        self.bytes_downloaded: int = 0
        self.started_at: float = time.monotonic()

        # Pre-prioritize first piece(s) and last piece (for MP4 moov header/footer)
        self._urgent_pieces.append(self.first_piece)
        if self.last_piece != self.first_piece:
            self._urgent_pieces.append(self.last_piece)

        self.output_path.parent.mkdir(parents=True, exist_ok=True)
        self._fd = os.open(
            str(self.output_path),
            os.O_CREAT | os.O_RDWR,
            0o644,
        )
        os.ftruncate(self._fd, self.target_file.length)

    def close(self) -> None:
        with self._lock:
            if self._fd >= 0:
                os.close(self._fd)
                self._fd = -1

    @property
    def is_complete(self) -> bool:
        with self._lock:
            return self.required_pieces.issubset(self.completed_pieces)

    @property
    def progress_fraction(self) -> float:
        with self._lock:
            if not self.required_pieces:
                return 1.0
            return len(self.completed_pieces & self.required_pieces) / len(self.required_pieces)

    def piece_states_snapshot(self) -> Dict[str, Any]:
        with self._lock:
            urgent_set = set(self._urgent_pieces)
            states = []
            for p in range(self.first_piece, self.last_piece + 1):
                if p in self.completed_pieces:
                    states.append("done")
                elif p in self.in_progress_pieces:
                    states.append("active")
                elif p in urgent_set:
                    states.append("urgent")
                else:
                    states.append("pending")
            elapsed = max(0.001, time.monotonic() - self.started_at)
            return {
                "total_pieces": len(self.required_pieces),
                "completed_pieces": len(self.completed_pieces & self.required_pieces),
                "progress": round(len(self.completed_pieces & self.required_pieces) / max(1, len(self.required_pieces)), 4),
                "complete": self.required_pieces.issubset(self.completed_pieces),
                "size": self.target_file.length,
                "bytes_downloaded": self.bytes_downloaded,
                "speed_bps": int(self.bytes_downloaded / elapsed),
                "piece_length": self.metadata.piece_length,
                "priority_cursor": self._priority_cursor,
                "pieces": states,
            }

    def piece_for_file_offset(self, file_byte_offset: int) -> int:
        global_offset = self.target_file.offset + max(0, min(file_byte_offset, self.target_file.length - 1))
        return global_offset // self.metadata.piece_length

    def prioritize_byte_range(self, start_byte: int, end_byte: int) -> None:
        start_piece = self.piece_for_file_offset(start_byte)
        end_piece = self.piece_for_file_offset(min(end_byte, start_byte + self.sliding_window_pieces * self.metadata.piece_length))
        with self._lock:
            self._priority_cursor = start_piece
            new_urgent = [
                p for p in range(start_piece, min(self.last_piece + 1, end_piece + self.sliding_window_pieces))
                if p not in self.completed_pieces
            ]
            for p in self._urgent_pieces:
                if p not in new_urgent and p not in self.completed_pieces:
                    new_urgent.append(p)
            self._urgent_pieces = new_urgent
            self._lock.notify_all()

    def next_piece_to_download(self, peer_bitfield: Optional[Set[int]] = None) -> Optional[int]:
        with self._lock:
            def eligible(p: int) -> bool:
                if p not in self.required_pieces:
                    return False
                if p in self.completed_pieces or p in self.in_progress_pieces:
                    return False
                if peer_bitfield is not None and p not in peer_bitfield:
                    return False
                return True

            while self._urgent_pieces and self._urgent_pieces[0] in self.completed_pieces:
                self._urgent_pieces.pop(0)
            for p in self._urgent_pieces:
                if eligible(p):
                    self.in_progress_pieces.add(p)
                    return p

            for p in range(self._priority_cursor, self.last_piece + 1):
                if eligible(p):
                    self.in_progress_pieces.add(p)
                    return p

            for p in range(self.first_piece, self._priority_cursor):
                if eligible(p):
                    self.in_progress_pieces.add(p)
                    return p

            return None

    def release_in_progress(self, piece_index: int) -> None:
        with self._lock:
            self.in_progress_pieces.discard(piece_index)
            self._lock.notify_all()

    def verify_and_store_piece(self, piece_index: int, data: bytes) -> bool:
        expected_hash = self.metadata.piece_hashes[piece_index]
        actual_hash = hashlib.sha1(data).digest()
        if actual_hash != expected_hash:
            self.release_in_progress(piece_index)
            return False

        piece_global_start = piece_index * self.metadata.piece_length
        piece_global_end = piece_global_start + len(data)

        file_global_start = self.target_file.offset
        file_global_end = file_global_start + self.target_file.length

        overlap_start = max(piece_global_start, file_global_start)
        overlap_end = min(piece_global_end, file_global_end)

        with self._lock:
            if overlap_start < overlap_end and self._fd >= 0:
                slice_start = overlap_start - piece_global_start
                slice_end = overlap_end - piece_global_start
                file_write_offset = overlap_start - file_global_start
                os.pwrite(self._fd, data[slice_start:slice_end], file_write_offset)

            if piece_index not in self.completed_pieces:
                self.bytes_downloaded += len(data)
            self.in_progress_pieces.discard(piece_index)
            self.completed_pieces.add(piece_index)
            self._lock.notify_all()
        return True

    def read_video_bytes(self, file_offset: int, length: int, timeout: float = 30.0) -> bytes:
        if file_offset >= self.target_file.length or length <= 0:
            return b""
        length = min(length, self.target_file.length - file_offset)
        end_offset = file_offset + length - 1

        start_piece = self.piece_for_file_offset(file_offset)
        end_piece = self.piece_for_file_offset(end_offset)
        needed = set(range(start_piece, end_piece + 1))

        self.prioritize_byte_range(file_offset, end_offset)

        deadline = time.monotonic() + timeout
        with self._lock:
            while not needed.issubset(self.completed_pieces):
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    missing = sorted(needed - self.completed_pieces)
                    raise TimeoutError(
                        f"Timed out waiting for pieces {missing} (offset={file_offset}, len={length})"
                    )
                self._lock.wait(timeout=min(0.25, remaining))
            return os.pread(self._fd, length, file_offset)


# ============================================================================
# 4. Trackers (HTTP + UDP BEP 0015) & Magnet Metadata Fetcher (BEP 0009/0010)
# ============================================================================

MSG_CHOKE = 0
MSG_UNCHOKE = 1
MSG_INTERESTED = 2
MSG_NOT_INTERESTED = 3
MSG_HAVE = 4
MSG_BITFIELD = 5
MSG_REQUEST = 6
MSG_PIECE = 7
MSG_CANCEL = 8
MSG_EXTENDED = 20  # BEP 0010 Extension Protocol

BLOCK_SIZE = 16384
METADATA_PIECE_SIZE = 16384


def query_http_tracker(
    announce_url: str,
    info_hash: bytes,
    peer_id: bytes,
    port: int,
    left: int,
    timeout: float = 4.0,
) -> List[Tuple[str, int]]:
    if not announce_url.startswith(("http://", "https://")):
        return []
    params = {
        "info_hash": info_hash,
        "peer_id": peer_id,
        "port": str(port),
        "uploaded": "0",
        "downloaded": "0",
        "left": str(left),
        "compact": "1",
    }
    sep = "&" if "?" in announce_url else "?"
    url = announce_url + sep + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={"User-Agent": "TorrentVideoTool/2.0"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        payload = bdecode(resp.read())

    peers_raw = payload.get(b"peers", b"")
    peers: List[Tuple[str, int]] = []
    if isinstance(peers_raw, bytes):
        for i in range(0, len(peers_raw), 6):
            chunk = peers_raw[i:i + 6]
            if len(chunk) == 6:
                ip = socket.inet_ntoa(chunk[:4])
                pport = struct.unpack("!H", chunk[4:6])[0]
                peers.append((ip, pport))
    elif isinstance(peers_raw, list):
        for pdict in peers_raw:
            ip = pdict[b"ip"].decode("utf-8")
            pport = int(pdict[b"port"])
            peers.append((ip, pport))
    return peers


def query_udp_tracker(
    announce_url: str,
    info_hash: bytes,
    peer_id: bytes,
    port: int = 6881,
    left: int = 0,
    timeout: float = 3.0,
) -> List[Tuple[str, int]]:
    """Query a UDP BitTorrent tracker using BEP 0015."""
    if not announce_url.startswith("udp://"):
        return []
    parsed = urllib.parse.urlsplit(announce_url)
    host = parsed.hostname
    uport = parsed.port or 80
    if not host:
        return []

    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
        sock.settimeout(timeout)
        addr = (socket.gethostbyname(host), uport)

        # 1. Connect request
        protocol_id = 0x41727101980
        tx_id = random.randint(0, 0x7FFFFFFF)
        conn_req = struct.pack("!QII", protocol_id, 0, tx_id)
        sock.sendto(conn_req, addr)
        data, _ = sock.recvfrom(2048)
        if len(data) < 16:
            return []
        action, rx_tx_id, conn_id = struct.unpack("!IIQ", data[:16])
        if action != 0 or rx_tx_id != tx_id:
            return []

        # 2. Announce request
        tx_id = random.randint(0, 0x7FFFFFFF)
        ann_req = struct.pack(
            "!QII20s20sQQQIIIiH",
            conn_id,
            1,  # announce action
            tx_id,
            info_hash,
            peer_id,
            0,  # downloaded
            left,
            0,  # uploaded
            0,  # event
            0,  # IP
            random.randint(0, 0x7FFFFFFF),
            50,  # num_want
            port,
        )
        sock.sendto(ann_req, addr)
        resp, _ = sock.recvfrom(4096)
        if len(resp) < 20:
            return []
        r_action, r_tx, _interval, _leechers, _seeders = struct.unpack("!IIIII", resp[:20])
        if r_action != 1 or r_tx != tx_id:
            return []

        peers_blob = resp[20:]
        peers: List[Tuple[str, int]] = []
        for i in range(0, len(peers_blob), 6):
            chunk = peers_blob[i:i + 6]
            if len(chunk) == 6:
                ip = socket.inet_ntoa(chunk[:4])
                pport = struct.unpack("!H", chunk[4:6])[0]
                if pport > 0:
                    peers.append((ip, pport))
        return peers


def discover_peers_from_trackers(
    trackers: List[str],
    info_hash: bytes,
    peer_id: bytes,
    left: int = 1048576,
) -> List[Tuple[str, int]]:
    discovered: List[Tuple[str, int]] = []
    for tr in trackers:
        try:
            if tr.startswith(("http://", "https://")):
                peers = query_http_tracker(tr, info_hash, peer_id, 6881, left)
            elif tr.startswith("udp://"):
                peers = query_udp_tracker(tr, info_hash, peer_id, 6881, left)
            else:
                peers = []
            for p in peers:
                if p not in discovered:
                    discovered.append(p)
        except Exception:
            continue
    return discovered


def _recv_exact(sock: socket.socket, n: int) -> bytes:
    buf = bytearray()
    while len(buf) < n:
        chunk = sock.recv(n - len(buf))
        if not chunk:
            raise ConnectionError("EOF while reading from peer socket")
        buf.extend(chunk)
    return bytes(buf)


def _send_msg(sock: socket.socket, msg_id: int, payload: bytes = b"") -> None:
    length = 1 + len(payload)
    sock.sendall(struct.pack("!IB", length, msg_id) + payload)


def fetch_magnet_metadata_from_peer(
    peer_addr: Tuple[str, int],
    info_hash: bytes,
    peer_id: bytes,
    timeout: float = 6.0,
) -> Optional[Dict[bytes, Any]]:
    """
    Resolve `.torrent` info dictionary from a peer using BEP 0010 (Extension Protocol)
    and BEP 0009 (`ut_metadata`). Verifies SHA-1(info_bytes) == info_hash.
    """
    with socket.create_connection(peer_addr, timeout=timeout) as sock:
        sock.settimeout(timeout)
        pstr = b"BitTorrent protocol"
        # Set BEP 0010 extension bit: reserved[5] = 0x10
        reserved = bytearray(8)
        reserved[5] = 0x10
        handshake = struct.pack("!B", len(pstr)) + pstr + bytes(reserved) + info_hash + peer_id
        sock.sendall(handshake)

        resp = _recv_exact(sock, 68)
        if resp[1:20] != pstr or resp[28:48] != info_hash:
            return None
        if (resp[25] & 0x10) == 0:
            return None  # Peer does not support BEP 0010 extensions

        # Send Extended Handshake advertising ut_metadata = 1
        ext_hs = bencode({b"m": {b"ut_metadata": 1}})
        _send_msg(sock, MSG_EXTENDED, struct.pack("!B", 0) + ext_hs)

        peer_ut_metadata_id: Optional[int] = None
        metadata_size: Optional[int] = None
        pieces: Dict[int, bytes] = {}
        num_meta_pieces = 0

        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            raw_len = _recv_exact(sock, 4)
            mlen = struct.unpack("!I", raw_len)[0]
            if mlen == 0:
                continue
            mid = _recv_exact(sock, 1)[0]
            payload = _recv_exact(sock, mlen - 1) if mlen > 1 else b""

            if mid == MSG_EXTENDED and len(payload) >= 1:
                ext_id = payload[0]
                ext_body = payload[1:]
                if ext_id == 0:
                    # Extended handshake from peer
                    hs_dict = bdecode(ext_body)
                    m_dict = hs_dict.get(b"m", {})
                    if b"ut_metadata" in m_dict:
                        peer_ut_metadata_id = int(m_dict[b"ut_metadata"])
                    if b"metadata_size" in hs_dict:
                        metadata_size = int(hs_dict[b"metadata_size"])
                    if peer_ut_metadata_id and metadata_size:
                        num_meta_pieces = (metadata_size + METADATA_PIECE_SIZE - 1) // METADATA_PIECE_SIZE
                        for idx in range(num_meta_pieces):
                            req_dict = bencode({b"msg_type": 0, b"piece": idx})
                            _send_msg(sock, MSG_EXTENDED, struct.pack("!B", peer_ut_metadata_id) + req_dict)
                elif ext_id == 1:
                    # Response for our ut_metadata id (1)
                    header_dict, piece_slice = bdecode_prefix(ext_body)
                    if header_dict.get(b"msg_type") == 1:
                        p_idx = int(header_dict[b"piece"])
                        pieces[p_idx] = piece_slice
                        if num_meta_pieces > 0 and len(pieces) == num_meta_pieces:
                            full_info_bytes = b"".join(pieces[i] for i in range(num_meta_pieces))
                            if hashlib.sha1(full_info_bytes).digest() == info_hash:
                                return bdecode(full_info_bytes)
                            return None
    return None


# ============================================================================
# 5. BitTorrent Peer Worker (BEP 0003)
# ============================================================================

class PeerWorker(threading.Thread):
    """Downloads pieces from a single BitTorrent peer using BEP 0003 wire protocol."""

    def __init__(
        self,
        peer_addr: Tuple[str, int],
        metadata: TorrentMetadata,
        store: SparseVideoPieceStore,
        peer_id: bytes,
        stop_event: threading.Event,
    ) -> None:
        super().__init__(daemon=True)
        self.peer_addr = peer_addr
        self.metadata = metadata
        self.store = store
        self.peer_id = peer_id
        self.stop_event = stop_event
        self.connected = False

    def run(self) -> None:
        while not self.stop_event.is_set() and not self.store.is_complete:
            try:
                self._session()
            except Exception:
                self.connected = False
                time.sleep(0.2)

    def _session(self) -> None:
        with socket.create_connection(self.peer_addr, timeout=5.0) as sock:
            sock.settimeout(5.0)
            pstr = b"BitTorrent protocol"
            handshake = struct.pack("!B", len(pstr)) + pstr + (b"\x00" * 8) + self.metadata.info_hash + self.peer_id
            sock.sendall(handshake)

            resp = _recv_exact(sock, 68)
            if resp[1:20] != pstr or resp[28:48] != self.metadata.info_hash:
                raise ConnectionError("Invalid peer handshake")

            self.connected = True
            _send_msg(sock, MSG_INTERESTED)

            peer_choking = True
            peer_pieces: Set[int] = set(range(self.metadata.num_pieces))

            while not self.stop_event.is_set() and not self.store.is_complete:
                if peer_choking:
                    msg_id, payload = self._read_message(sock)
                    if msg_id == MSG_UNCHOKE:
                        peer_choking = False
                    elif msg_id == MSG_CHOKE:
                        peer_choking = True
                    elif msg_id == MSG_HAVE:
                        idx = struct.unpack("!I", payload[:4])[0]
                        peer_pieces.add(idx)
                    elif msg_id == MSG_BITFIELD:
                        peer_pieces = self._parse_bitfield(payload)
                    continue

                piece_idx = self.store.next_piece_to_download(peer_pieces)
                if piece_idx is None:
                    time.sleep(0.05)
                    continue

                try:
                    piece_data = self._download_piece(sock, piece_idx)
                    if piece_data is not None:
                        self.store.verify_and_store_piece(piece_idx, piece_data)
                    else:
                        peer_choking = True
                        self.store.release_in_progress(piece_idx)
                except Exception:
                    self.store.release_in_progress(piece_idx)
                    raise

    def _parse_bitfield(self, bitfield: bytes) -> Set[int]:
        available: Set[int] = set()
        for piece_idx in range(self.metadata.num_pieces):
            byte_idx = piece_idx // 8
            bit_idx = 7 - (piece_idx % 8)
            if byte_idx < len(bitfield) and (bitfield[byte_idx] & (1 << bit_idx)):
                available.add(piece_idx)
        return available

    def _read_message(self, sock: socket.socket) -> Tuple[int, bytes]:
        while True:
            length_bytes = _recv_exact(sock, 4)
            length = struct.unpack("!I", length_bytes)[0]
            if length == 0:
                continue
            msg_id = _recv_exact(sock, 1)[0]
            payload = _recv_exact(sock, length - 1) if length > 1 else b""
            return msg_id, payload

    def _download_piece(self, sock: socket.socket, piece_idx: int) -> Optional[bytes]:
        plen = self.metadata.piece_size(piece_idx)
        piece_buf = bytearray(plen)
        received = 0

        for begin in range(0, plen, BLOCK_SIZE):
            blen = min(BLOCK_SIZE, plen - begin)
            req_payload = struct.pack("!III", piece_idx, begin, blen)
            _send_msg(sock, MSG_REQUEST, req_payload)

        while received < plen:
            msg_id, payload = self._read_message(sock)
            if msg_id == MSG_CHOKE:
                return None
            if msg_id == MSG_PIECE:
                r_idx, r_begin = struct.unpack("!II", payload[:8])
                block = payload[8:]
                if r_idx == piece_idx:
                    piece_buf[r_begin:r_begin + len(block)] = block
                    received += len(block)
        return bytes(piece_buf)


# ============================================================================
# 6. Embedded Seeder (Supports BEP 0003 Pieces + BEP 0009/0010 Magnet Metadata!)
# ============================================================================

class _EmbeddedFixtureSeeder:
    """
    Local BEP 0003 + BEP 0009/0010 (`ut_metadata`) TCP Seeder.
    Allows both `.torrent` files and `magnet:?xt=urn:btih:...` links to resolve metadata
    and stream/download video pieces over real BitTorrent wire protocol!
    """

    def __init__(
        self,
        info_hash: bytes,
        payload: bytes,
        piece_length: int,
        raw_info_bytes: bytes = b"",
        piece_delay_sec: float = 0.0,
    ) -> None:
        self.info_hash = info_hash
        self.payload = payload
        self.piece_length = piece_length
        self.raw_info_bytes = raw_info_bytes
        self.piece_delay_sec = piece_delay_sec
        self.num_pieces = (len(payload) + piece_length - 1) // piece_length
        self._sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self._sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self._sock.bind(("127.0.0.1", 0))
        self._sock.listen(16)
        self.host, self.port = self._sock.getsockname()[:2]
        self._stop = threading.Event()
        threading.Thread(target=self._accept_loop, daemon=True).start()

    def _accept_loop(self) -> None:
        self._sock.settimeout(0.2)
        while not self._stop.is_set():
            try:
                conn, _ = self._sock.accept()
            except socket.timeout:
                continue
            except OSError:
                break
            threading.Thread(target=self._serve_peer, args=(conn,), daemon=True).start()

    def _serve_peer(self, conn: socket.socket) -> None:
        with conn:
            conn.settimeout(5.0)
            try:
                hs = _recv_exact(conn, 68)
                if hs[28:48] != self.info_hash:
                    return
                reserved = bytearray(8)
                reserved[5] = 0x10  # Advertise BEP 0010 extension support
                conn.sendall(hs[:20] + bytes(reserved) + self.info_hash + b"-SD0001-MAGNETSEEDER")
                bf = bytes([0xFF] * ((self.num_pieces + 7) // 8))
                _send_msg(conn, MSG_BITFIELD, bf)

                peer_ut_metadata_id = 1
                while not self._stop.is_set():
                    raw_len = _recv_exact(conn, 4)
                    mlen = struct.unpack("!I", raw_len)[0]
                    if mlen == 0:
                        continue
                    mid = _recv_exact(conn, 1)[0]
                    pl = _recv_exact(conn, mlen - 1) if mlen > 1 else b""
                    if mid == MSG_INTERESTED:
                        _send_msg(conn, MSG_UNCHOKE)
                    elif mid == MSG_EXTENDED and len(pl) >= 1:
                        ext_id = pl[0]
                        ext_body = pl[1:]
                        if ext_id == 0:
                            hs_dict = bdecode(ext_body)
                            m_dict = hs_dict.get(b"m", {})
                            if b"ut_metadata" in m_dict:
                                peer_ut_metadata_id = int(m_dict[b"ut_metadata"])
                            reply = bencode({
                                b"m": {b"ut_metadata": 1},
                                b"metadata_size": len(self.raw_info_bytes),
                            })
                            _send_msg(conn, MSG_EXTENDED, struct.pack("!B", 0) + reply)
                        elif ext_id == 1 and self.raw_info_bytes:
                            req_d, _ = bdecode_prefix(ext_body)
                            if req_d.get(b"msg_type") == 0:
                                p_idx = int(req_d[b"piece"])
                                start = p_idx * METADATA_PIECE_SIZE
                                chunk = self.raw_info_bytes[start:start + METADATA_PIECE_SIZE]
                                resp_hdr = bencode({
                                    b"msg_type": 1,
                                    b"piece": p_idx,
                                    b"total_size": len(self.raw_info_bytes),
                                })
                                _send_msg(
                                    conn,
                                    MSG_EXTENDED,
                                    struct.pack("!B", peer_ut_metadata_id) + resp_hdr + chunk,
                                )
                    elif mid == MSG_REQUEST:
                        p_idx, begin, length = struct.unpack("!III", pl[:12])
                        if self.piece_delay_sec > 0 and begin == 0:
                            time.sleep(self.piece_delay_sec)
                        start = p_idx * self.piece_length + begin
                        block = self.payload[start:start + length]
                        _send_msg(conn, MSG_PIECE, struct.pack("!II", p_idx, begin) + block)
            except Exception:
                return

    def stop(self) -> None:
        self._stop.set()
        try:
            self._sock.close()
        except OSError:
            pass


# Global registry of embedded fixture seeders by info_hash hex so pasted magnet links
# even without x.pe can discover the local fixture seeder immediately.
_GLOBAL_FIXTURE_SEEDERS: Dict[str, _EmbeddedFixtureSeeder] = {}


def ensure_demo_fixture(torrent_path: Path, total_size: int = 1024 * 1024, piece_length: int = 32768) -> Path:
    """
    Ensure a playable MP4 video payload and `.torrent` file exist at `torrent_path`.
    Uses `fixtures/fixture_video.mp4` (real H.264 MP4 generated on macOS if available)
    so browser `<video>` playback shows an animated video stream.
    """
    payload_path = torrent_path.with_suffix(".payload")
    real_mp4 = Path(__file__).resolve().parent / "fixtures" / "fixture_video.mp4"

    if real_mp4.exists() and real_mp4.stat().st_size > 10000:
        video_bytes = real_mp4.read_bytes()
    elif payload_path.exists():
        video_bytes = payload_path.read_bytes()
    else:
        ftyp = struct.pack("!I4s", 28, b"ftyp") + b"isom\x00\x00\x02\x00isomiso2mp41"
        moov_body = b"moov-index-table:" + hashlib.sha256(b"mp4-index").digest() * 8
        moov = struct.pack("!I4s", 8 + len(moov_body), b"moov") + moov_body
        mdat_len = max(64, total_size - len(ftyp) - len(moov) - 8)
        block_seed = hashlib.sha512(b"fixture-video-frames").digest()
        mdat_payload = (block_seed * ((mdat_len // len(block_seed)) + 1))[:mdat_len]
        mdat = struct.pack("!I4s", 8 + len(mdat_payload), b"mdat") + mdat_payload
        video_bytes = ftyp + mdat + moov

    torrent_path.parent.mkdir(parents=True, exist_ok=True)
    pieces = [
        hashlib.sha1(video_bytes[i:i + piece_length]).digest()
        for i in range(0, len(video_bytes), piece_length)
    ]
    info_dict = {
        b"name": b"fixture_video.mp4",
        b"piece length": piece_length,
        b"pieces": b"".join(pieces),
        b"length": len(video_bytes),
    }
    torrent_dict = {
        b"announce": b"http://127.0.0.1:0/announce",
        b"info": info_dict,
    }
    torrent_path.write_bytes(bencode(torrent_dict))
    payload_path.write_bytes(video_bytes)

    info_bytes = bencode(info_dict)
    info_hash = hashlib.sha1(info_bytes).digest()
    if info_hash.hex() not in _GLOBAL_FIXTURE_SEEDERS:
        _GLOBAL_FIXTURE_SEEDERS[info_hash.hex()] = _EmbeddedFixtureSeeder(
            info_hash=info_hash,
            payload=video_bytes,
            piece_length=piece_length,
            raw_info_bytes=info_bytes,
            piece_delay_sec=0.02,  # Slight pacing so UI piece map animation is visible
        )
    return torrent_path


def get_default_fixture_magnet() -> str:
    """Return a ready-to-paste `magnet:?xt=urn:btih:...` URI backed by our local BEP 0009 seeder."""
    fixture_torrent = Path(__file__).resolve().parent / "fixtures" / "video.torrent"
    ensure_demo_fixture(fixture_torrent)
    meta = TorrentMetadata.from_file(fixture_torrent)
    seeder = _GLOBAL_FIXTURE_SEEDERS[meta.info_hash.hex()]
    return meta.to_magnet_uri(extra_peers=[(seeder.host, seeder.port)])


DEFAULT_PUBLIC_TRACKERS = [
    "udp://tracker.opentrackr.org:1337/announce",
    "udp://open.stealth.si:80/announce",
    "udp://tracker.torrent.eu.org:451/announce",
    "udp://exodus.desync.com:6969/announce",
    "http://tracker.opentrackr.org:1337/announce",
]

DHT_BOOTSTRAP_NODES = [
    ("router.bittorrent.com", 6881),
    ("dht.transmissionbt.com", 6881),
    ("router.utorrent.com", 6881),
]


def query_dht_for_peers(info_hash: bytes, timeout: float = 3.5) -> List[Tuple[str, int]]:
    """
    Lightweight BEP 0005 Mainline DHT `get_peers` crawler over UDP.
    Queries bootstrap nodes and traverses closer Kademlia nodes to discover compact peers.
    """
    node_id = os.urandom(20)
    peers: List[Tuple[str, int]] = []
    visited: Set[Tuple[str, int]] = set()
    queue: List[Tuple[str, int]] = []

    for host, port in DHT_BOOTSTRAP_NODES:
        try:
            ip = socket.gethostbyname(host)
            queue.append((ip, port))
        except Exception:
            continue

    if not queue:
        return []

    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
        sock.settimeout(0.25)
        deadline = time.monotonic() + timeout

        while time.monotonic() < deadline and len(peers) < 30:
            batch = []
            while queue and len(batch) < 12:
                addr = queue.pop(0)
                if addr not in visited:
                    visited.add(addr)
                    batch.append(addr)

            for addr in batch:
                query = bencode({
                    b"t": os.urandom(2),
                    b"y": b"q",
                    b"q": b"get_peers",
                    b"a": {b"id": node_id, b"info_hash": info_hash},
                })
                try:
                    sock.sendto(query, addr)
                except Exception:
                    pass

            read_until = time.monotonic() + 0.35
            while time.monotonic() < read_until:
                try:
                    data, _ = sock.recvfrom(4096)
                    msg = bdecode(data)
                    if not isinstance(msg, dict):
                        continue
                    r = msg.get(b"r")
                    if not isinstance(r, dict):
                        continue
                    # Direct peer values found!
                    if b"values" in r and isinstance(r[b"values"], list):
                        for item in r[b"values"]:
                            if isinstance(item, bytes) and len(item) == 6:
                                ip = socket.inet_ntoa(item[:4])
                                pport = struct.unpack("!H", item[4:6])[0]
                                if pport > 0 and (ip, pport) not in peers:
                                    peers.append((ip, pport))
                    # Closer DHT nodes to query next
                    if b"nodes" in r and isinstance(r[b"nodes"], bytes):
                        nodes_blob = r[b"nodes"]
                        for i in range(0, len(nodes_blob), 26):
                            chunk = nodes_blob[i:i + 26]
                            if len(chunk) == 26:
                                nip = socket.inet_ntoa(chunk[20:24])
                                nport = struct.unpack("!H", chunk[24:26])[0]
                                if nport > 0 and (nip, nport) not in visited:
                                    queue.append((nip, nport))
                except socket.timeout:
                    break
                except Exception:
                    continue

    return peers


# ============================================================================
# 7. High-Level Session Supporting BOTH `.torrent` Files AND `magnet:` Links
# ============================================================================

class TorrentVideoSession:
    """Orchestrates magnet/torrent resolution, peer connections, download, and HTTP streaming."""

    def __init__(
        self,
        source: str | Path,
        output_dir: str | Path,
        peers: Optional[List[Tuple[str, int]]] = None,
        sliding_window_pieces: int = 8,
    ) -> None:
        self.source_str = str(source).strip()
        self.output_dir = Path(output_dir)
        self.peer_id = b"-TV0002-" + os.urandom(12)
        self.explicit_peers = list(peers) if peers else []
        self.stop_event = threading.Event()
        self.workers: List[PeerWorker] = []
        self.stream_server: Optional[VideoStreamServer] = None
        self._embedded_seeder: Optional[_EmbeddedFixtureSeeder] = None

        if self.source_str.startswith("magnet:?"):
            self.metadata, discovered_peers = self._resolve_magnet(self.source_str)
            for p in discovered_peers:
                if p not in self.explicit_peers:
                    self.explicit_peers.append(p)
            self.torrent_path: Optional[Path] = None
        else:
            self.torrent_path = Path(self.source_str)
            if not self.torrent_path.exists():
                print(f"[Fixture] Generating local test fixture torrent at: {self.torrent_path}")
                ensure_demo_fixture(self.torrent_path)
            else:
                payload_candidate = self.torrent_path.with_suffix(".payload")
                if payload_candidate.exists():
                    ensure_demo_fixture(self.torrent_path)
            self.metadata = TorrentMetadata.from_file(self.torrent_path)

        self.target_file = self.metadata.select_video_file()
        self.output_path = self.output_dir / Path(self.target_file.path).name
        self.store = SparseVideoPieceStore(
            self.metadata,
            self.target_file,
            self.output_path,
            sliding_window_pieces=sliding_window_pieces,
        )

    def _resolve_magnet(self, magnet_uri: str) -> Tuple[TorrentMetadata, List[Tuple[str, int]]]:
        """
        Resolve a Magnet URI via:
        1. Explicit `x.pe` peers or registered local fixture seeder
        2. Magnet `tr=` HTTP & UDP (BEP 0015) trackers + public tracker fallback list
        3. Mainline DHT (BEP 0005 `get_peers`)
        4. BEP 0009/0010 (`ut_metadata`) exchange over TCP
        """
        m_info = parse_magnet_uri(magnet_uri)
        candidates = list(m_info.explicit_peers)

        # Ensure default fixture is initialized in case the user pasted the fixture hash
        get_default_fixture_magnet()
        if m_info.info_hash.hex() in _GLOBAL_FIXTURE_SEEDERS:
            seeder = _GLOBAL_FIXTURE_SEEDERS[m_info.info_hash.hex()]
            if (seeder.host, seeder.port) not in candidates:
                candidates.insert(0, (seeder.host, seeder.port))

        # Combine magnet trackers with public fallback trackers if needed
        trackers = list(m_info.trackers)
        if not candidates:
            for pub_tr in DEFAULT_PUBLIC_TRACKERS:
                if pub_tr not in trackers:
                    trackers.append(pub_tr)

        if trackers and not (m_info.info_hash.hex() in _GLOBAL_FIXTURE_SEEDERS):
            tracker_peers = discover_peers_from_trackers(
                trackers, m_info.info_hash, self.peer_id
            )
            for tp in tracker_peers:
                if tp not in candidates:
                    candidates.append(tp)

        if not candidates:
            dht_peers = query_dht_for_peers(m_info.info_hash, timeout=3.5)
            for dp in dht_peers:
                if dp not in candidates:
                    candidates.append(dp)

        # Fetch info dictionary via BEP 0009/0010 ut_metadata from candidate peers
        for peer_addr in candidates[:25]:
            try:
                info_dict = fetch_magnet_metadata_from_peer(
                    peer_addr, m_info.info_hash, self.peer_id, timeout=3.5
                )
                if info_dict is not None:
                    meta = TorrentMetadata.from_info_dict(
                        info_dict,
                        announce=trackers[0] if trackers else "",
                        announce_list=trackers,
                    )
                    return meta, candidates
            except Exception:
                continue

        raise RuntimeError(
            f"No active TCP peers responded with BEP 0009 ut_metadata for info_hash={m_info.info_hash.hex()} "
            f"(checked {len(trackers)} trackers, DHT, and {len(candidates)} peers). "
            "Click '🧪 Load Test Fixture Magnet Link' or upload a .torrent file to test immediately."
        )

    def start_swarm(self) -> None:
        discovered = list(self.explicit_peers)
        if self.metadata.announce_list and self.metadata.info_hash.hex() not in _GLOBAL_FIXTURE_SEEDERS:
            for p in discover_peers_from_trackers(
                self.metadata.announce_list,
                self.metadata.info_hash,
                self.peer_id,
                left=self.target_file.length,
            ):
                if p not in discovered:
                    discovered.append(p)

        if not discovered and self.metadata.info_hash.hex() in _GLOBAL_FIXTURE_SEEDERS:
            seeder = _GLOBAL_FIXTURE_SEEDERS[self.metadata.info_hash.hex()]
            discovered.append((seeder.host, seeder.port))

        if not discovered and self.torrent_path is not None:
            candidate_payload = self.torrent_path.with_suffix(".payload")
            if candidate_payload.exists():
                self._embedded_seeder = _EmbeddedFixtureSeeder(
                    info_hash=self.metadata.info_hash,
                    payload=candidate_payload.read_bytes(),
                    piece_length=self.metadata.piece_length,
                    raw_info_bytes=self.metadata.raw_info_bytes,
                )
                discovered.append((self._embedded_seeder.host, self._embedded_seeder.port))

        for peer_addr in discovered[:20]:
            worker = PeerWorker(
                peer_addr=peer_addr,
                metadata=self.metadata,
                store=self.store,
                peer_id=self.peer_id,
                stop_event=self.stop_event,
            )
            worker.start()
            self.workers.append(worker)

    def start_http_stream(self, host: str = "127.0.0.1", port: int = 0) -> str:
        self.stream_server = VideoStreamServer(self.store, host=host, port=port, session=self)
        return self.stream_server.start()

    def wait_until_complete(self, timeout: float = 60.0) -> bool:
        deadline = time.monotonic() + timeout
        while not self.store.is_complete:
            if time.monotonic() >= deadline:
                return False
            time.sleep(0.05)
        return True

    def close(self) -> None:
        self.stop_event.set()
        if self.stream_server is not None:
            self.stream_server.stop()
        if self._embedded_seeder is not None:
            self._embedded_seeder.stop()
        self.store.close()


# ============================================================================
# 8. Interactive Web UI & HTTP 206 Range Video Streaming Server
# ============================================================================

WEB_UI_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>BitTorrent Magnet & Video Streamer</title>
  <style>
    :root {
      --bg: #0b0f19;
      --panel: #131b2e;
      --border: #23304f;
      --accent: #3b82f6;
      --accent-hover: #2563eb;
      --emerald: #10b981;
      --amber: #f59e0b;
      --text: #f1f5f9;
      --muted: #94a3b8;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
      background: radial-gradient(circle at top, #172554 0%, var(--bg) 55%);
      color: var(--text);
      min-height: 100vh;
      padding: 28px 18px;
    }
    .container {
      max-width: 1040px;
      margin: 0 auto;
    }
    header {
      display: flex;
      align-items: center;
      justify-content: space-between;
      flex-wrap: wrap;
      gap: 12px;
      margin-bottom: 22px;
    }
    h1 {
      margin: 0;
      font-size: 1.55rem;
      letter-spacing: -0.02em;
      display: flex;
      align-items: center;
      gap: 10px;
    }
    .badge {
      font-size: 0.75rem;
      background: rgba(59, 130, 246, 0.18);
      color: #93c5fd;
      border: 1px solid rgba(59, 130, 246, 0.4);
      padding: 4px 10px;
      border-radius: 999px;
      font-weight: 600;
    }
    .card {
      background: var(--panel);
      border: 1px solid var(--border);
      border-radius: 14px;
      padding: 20px;
      margin-bottom: 20px;
      box-shadow: 0 12px 32px rgba(0, 0, 0, 0.35);
    }
    label {
      display: block;
      font-size: 0.85rem;
      font-weight: 600;
      color: var(--muted);
      margin-bottom: 8px;
      text-transform: uppercase;
      letter-spacing: 0.04em;
    }
    .input-row {
      display: flex;
      gap: 10px;
      flex-wrap: wrap;
    }
    input[type="text"] {
      flex: 1;
      min-width: 260px;
      background: #090d16;
      border: 1px solid var(--border);
      color: var(--text);
      padding: 12px 14px;
      border-radius: 10px;
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      font-size: 0.88rem;
      outline: none;
    }
    input[type="text"]:focus {
      border-color: var(--accent);
      box-shadow: 0 0 0 3px rgba(59, 130, 246, 0.2);
    }
    .btn-row {
      display: flex;
      gap: 10px;
      margin-top: 14px;
      flex-wrap: wrap;
      align-items: center;
    }
    button, .btn-link {
      cursor: pointer;
      border: none;
      border-radius: 10px;
      padding: 11px 18px;
      font-size: 0.92rem;
      font-weight: 600;
      display: inline-flex;
      align-items: center;
      gap: 8px;
      transition: all 0.15s ease;
      text-decoration: none;
    }
    .btn-stream {
      background: var(--accent);
      color: white;
    }
    .btn-stream:hover { background: var(--accent-hover); }
    .btn-download {
      background: var(--emerald);
      color: #052e16;
    }
    .btn-download:hover { filter: brightness(1.1); }
    .btn-fixture {
      background: #1e293b;
      color: #cbd5e1;
      border: 1px solid #334155;
      font-size: 0.84rem;
      padding: 9px 14px;
    }
    .btn-fixture:hover { background: #334155; color: white; }
    .grid-2 {
      display: grid;
      grid-template-columns: 1.35fr 1fr;
      gap: 20px;
    }
    @media (max-width: 820px) {
      .grid-2 { grid-template-columns: 1fr; }
    }
    video {
      width: 100%;
      border-radius: 10px;
      background: #000;
      border: 1px solid var(--border);
      aspect-ratio: 16 / 9;
    }
    .stats-grid {
      display: grid;
      grid-template-columns: repeat(2, 1fr);
      gap: 10px;
      margin-bottom: 14px;
    }
    .stat-box {
      background: #090d16;
      border: 1px solid var(--border);
      border-radius: 10px;
      padding: 10px 12px;
    }
    .stat-label {
      font-size: 0.74rem;
      color: var(--muted);
      text-transform: uppercase;
    }
    .stat-value {
      font-size: 1.05rem;
      font-weight: 700;
      margin-top: 3px;
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      word-break: break-all;
    }
    .progress-bar-bg {
      height: 10px;
      background: #090d16;
      border-radius: 999px;
      overflow: hidden;
      border: 1px solid var(--border);
      margin: 12px 0;
    }
    .progress-bar-fill {
      height: 100%;
      width: 0%;
      background: linear-gradient(90deg, var(--accent), var(--emerald));
      transition: width 0.25s ease;
    }
    .piece-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(14px, 1fr));
      gap: 4px;
      margin-top: 10px;
      max-height: 170px;
      overflow-y: auto;
      padding: 8px;
      background: #090d16;
      border-radius: 8px;
      border: 1px solid var(--border);
    }
    .piece-cell {
      height: 14px;
      border-radius: 3px;
      background: #1e293b;
      transition: background 0.15s;
    }
    .piece-cell.done { background: var(--emerald); }
    .piece-cell.urgent { background: var(--amber); }
    .piece-cell.active { background: var(--accent); }
    .legend {
      display: flex;
      gap: 14px;
      font-size: 0.78rem;
      color: var(--muted);
      margin-top: 8px;
    }
    .dot {
      display: inline-block;
      width: 9px;
      height: 9px;
      border-radius: 2px;
      margin-right: 5px;
    }
    .status-banner {
      margin-top: 12px;
      padding: 10px 14px;
      border-radius: 8px;
      font-size: 0.88rem;
      background: rgba(16, 185, 129, 0.12);
      border: 1px solid rgba(16, 185, 129, 0.35);
      color: #a7f3d0;
      display: none;
    }
    .error-banner {
      margin-top: 12px;
      padding: 10px 14px;
      border-radius: 8px;
      font-size: 0.88rem;
      background: rgba(239, 68, 68, 0.15);
      border: 1px solid rgba(239, 68, 68, 0.4);
      color: #fecaca;
      display: none;
    }
  </style>
</head>
<body>
  <div class="container">
    <header>
      <h1>⚡ BitTorrent Magnet Video Streamer & Downloader</h1>
      <span class="badge">BEP 0003 + BEP 0009 Magnet + DHT + HTTP 206 Range</span>
    </header>

    <div class="card">
      <label for="magnetInput">Paste Magnet Link (<code>magnet:?xt=urn:btih:...</code>) or Local <code>.torrent</code> Path</label>
      <div class="input-row">
        <input
          id="magnetInput"
          type="text"
          placeholder="magnet:?xt=urn:btih:... or path/to/video.torrent"
        />
        <input id="torrentFileInput" type="file" accept=".torrent" style="display:none" onchange="uploadTorrentFile(this)" />
        <button class="btn-fixture" onclick="document.getElementById('torrentFileInput').click()">📂 Upload .torrent</button>
      </div>
      <div class="btn-row">
        <button class="btn-stream" onclick="startSession('stream')">▶ Stream Video Now</button>
        <button class="btn-download" onclick="startSession('download')">⬇ Download Video</button>
        <button class="btn-fixture" onclick="loadFixtureMagnet()">🧪 Load Test Fixture Magnet Link</button>
        <a id="saveDiskLink" class="btn-link btn-fixture" style="display:none;" href="/download" download>💾 Save File to Browser</a>
      </div>
      <div id="statusBanner" class="status-banner"></div>
      <div id="errorBanner" class="error-banner"></div>
    </div>

    <div class="grid-2">
      <div class="card">
        <label>Live HTTP 206 Range Video Player (Supports Arbitrary Seeking)</label>
        <video id="videoPlayer" controls playsinline></video>
      </div>

      <div class="card">
        <label>Swarm & Piece Scheduler Telemetry</label>
        <div class="stats-grid">
          <div class="stat-box">
            <div class="stat-label">Target Video</div>
            <div id="statName" class="stat-value">—</div>
          </div>
          <div class="stat-box">
            <div class="stat-label">Video Size</div>
            <div id="statSize" class="stat-value">—</div>
          </div>
          <div class="stat-box">
            <div class="stat-label">Info Hash (BTIH)</div>
            <div id="statHash" class="stat-value" style="font-size:0.78rem;">—</div>
          </div>
          <div class="stat-box">
            <div class="stat-label">Download Progress</div>
            <div id="statProgress" class="stat-value">0%</div>
          </div>
        </div>

        <div class="progress-bar-bg">
          <div id="progressBar" class="progress-bar-fill"></div>
        </div>

        <label style="margin-top:14px;">Sparse Piece Map (Real-time SHA-1 Verified Pieces)</label>
        <div id="pieceGrid" class="piece-grid"></div>
        <div class="legend">
          <span><i class="dot" style="background:#10b981;"></i>Verified (SHA-1)</span>
          <span><i class="dot" style="background:#3b82f6;"></i>In-Flight</span>
          <span><i class="dot" style="background:#f59e0b;"></i>Seek Priority Window</span>
          <span><i class="dot" style="background:#1e293b;"></i>Sparse / Pending</span>
        </div>
      </div>
    </div>
  </div>

  <script>
    let pollTimer = null;

    async function loadFixtureMagnet() {
      const res = await fetch('/api/fixture-magnet');
      const data = await res.json();
      document.getElementById('magnetInput').value = data.magnet;
      showStatus('Loaded playable H.264 MP4 Test Fixture Magnet Link (BEP 0009 ut_metadata ready). Click Stream or Download!');
    }

    async function uploadTorrentFile(input) {
      if (!input.files || !input.files[0]) return;
      const file = input.files[0];
      const buf = await file.arrayBuffer();
      const res = await fetch('/api/upload-torrent?name=' + encodeURIComponent(file.name), {
        method: 'POST',
        body: buf
      });
      const data = await res.json();
      if (data.path) {
        document.getElementById('magnetInput').value = data.path;
        showStatus('Uploaded ' + file.name + '. Click Stream Video Now or Download Video!');
      }
    }

    function showStatus(msg) {
      const el = document.getElementById('statusBanner');
      const err = document.getElementById('errorBanner');
      err.style.display = 'none';
      el.textContent = msg;
      el.style.display = 'block';
    }

    function showError(msg) {
      const el = document.getElementById('statusBanner');
      const err = document.getElementById('errorBanner');
      el.style.display = 'none';
      err.textContent = msg;
      err.style.display = 'block';
    }

    function formatBytes(bytes) {
      if (!bytes) return '0 B';
      const units = ['B', 'KiB', 'MiB', 'GiB'];
      let i = 0;
      let val = bytes;
      while (val >= 1024 && i < units.length - 1) { val /= 1024; i++; }
      return val.toFixed(2) + ' ' + units[i];
    }

    async function startSession(mode) {
      window._dlTriggered = false;
      const source = document.getElementById('magnetInput').value.trim();
      if (!source) {
        await loadFixtureMagnet();
      }
      const finalSource = document.getElementById('magnetInput').value.trim();
      showStatus(mode === 'stream'
        ? 'Resolving Magnet / Torrent metadata & starting HTTP 206 Range stream...'
        : 'Resolving Magnet / Torrent metadata & downloading verified pieces...');

      try {
        const res = await fetch('/api/start', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({ source: finalSource, mode })
        });
        const data = await res.json();
        if (!res.ok || data.error) {
          showError(data.error || 'Failed to start torrent session');
          return;
        }

        document.getElementById('statName').textContent = data.file_name;
        document.getElementById('statSize').textContent = formatBytes(data.size);
        document.getElementById('statHash').textContent = data.info_hash;
        document.getElementById('saveDiskLink').style.display = 'inline-flex';
        document.getElementById('saveDiskLink').href = '/download?t=' + Date.now();

        if (mode === 'stream') {
          const video = document.getElementById('videoPlayer');
          video.src = '/stream?t=' + Date.now();
          video.play().catch(() => {});
          showStatus('Streaming live via HTTP 206 Partial Content! Seek anywhere on the video timeline.');
        } else {
          showStatus('Downloading full video to ' + data.output_path + ' ...');
        }

        if (pollTimer) clearInterval(pollTimer);
        pollStatus(mode);
        pollTimer = setInterval(() => pollStatus(mode), 250);
      } catch (e) {
        showError('Error communicating with server: ' + e.message);
      }
    }

    async function pollStatus(mode) {
      try {
        const res = await fetch('/status');
        if (!res.ok) return;
        const st = await res.json();
        if (!st.active) return;

        const pct = Math.round((st.progress || 0) * 100);
        document.getElementById('statProgress').textContent =
          pct + '% (' + st.completed_pieces + '/' + st.total_pieces + ' pieces)';
        document.getElementById('progressBar').style.width = pct + '%';

        const grid = document.getElementById('pieceGrid');
        if (st.pieces) {
          if (grid.children.length !== st.pieces.length) {
            grid.innerHTML = '';
            for (let i = 0; i < st.pieces.length; i++) {
              const cell = document.createElement('div');
              cell.className = 'piece-cell ' + st.pieces[i];
              cell.title = 'Piece #' + i;
              grid.appendChild(cell);
            }
          } else {
            for (let i = 0; i < st.pieces.length; i++) {
              grid.children[i].className = 'piece-cell ' + st.pieces[i];
            }
          }
        }

        if (st.complete && mode === 'download' && !window._dlTriggered) {
          window._dlTriggered = true;
          showStatus('Download 100% SHA-1 Verified! Saved to ' + st.output_path + '. Triggering browser download...');
          const a = document.createElement('a');
          a.href = '/download';
          a.download = st.file_name || 'video.mp4';
          document.body.appendChild(a);
          a.click();
          a.remove();
        }
      } catch (_) {}
    }

    window.addEventListener('DOMContentLoaded', async () => {
      await loadFixtureMagnet();
      const res = await fetch('/status');
      const st = await res.json();
      if (st.active) {
        document.getElementById('statName').textContent = st.file_name;
        document.getElementById('statSize').textContent = formatBytes(st.size);
        document.getElementById('statHash').textContent = st.info_hash;
        document.getElementById('saveDiskLink').style.display = 'inline-flex';
        const video = document.getElementById('videoPlayer');
        video.src = '/stream';
        pollTimer = setInterval(() => pollStatus('stream'), 250);
      }
    });
  </script>
</body>
</html>
"""


class _ThreadingHTTPServer(socketserver.ThreadingMixIn, http.server.HTTPServer):
    daemon_threads = True
    allow_reuse_address = True

    def handle_error(self, request: Any, client_address: Any) -> None:
        """
        Silently ignore normal browser `<video>` byte-range socket aborts
        (`ConnectionResetError`, `BrokenPipeError`, `ConnectionAbortedError`, `TimeoutError`).
        """
        exc_type, exc, _ = sys.exc_info()
        if isinstance(exc, (ConnectionResetError, BrokenPipeError, ConnectionAbortedError, TimeoutError, OSError)):
            return
        super().handle_error(request, client_address)


class VideoStreamServer:
    """
    HTTP Server providing:
    - `GET /` : Interactive Web UI to paste magnet links and stream/download videos
    - `GET /api/fixture-magnet` : Returns a live `magnet:?xt=urn:btih:...` test fixture URI
    - `POST /api/upload-torrent` : Uploads a `.torrent` file from browser
    - `POST /api/start` : Starts a new `TorrentVideoSession` from any magnet URI or `.torrent` path
    - `GET /stream` : HTTP 206 Partial Content Range video streamer
    - `GET /download` : Direct attachment download of the verified video file
    - `GET /status` : Real-time JSON telemetry and piece state array
    """

    def __init__(
        self,
        store: Optional[SparseVideoPieceStore] = None,
        host: str = "127.0.0.1",
        port: int = 0,
        stream_chunk_size: int = 65536,
        output_dir: str | Path = "./downloads",
        session: Optional[TorrentVideoSession] = None,
    ) -> None:
        self.store = store
        self.active_session = session
        self.host = host
        self.port = port
        self.stream_chunk_size = stream_chunk_size
        self.output_dir = Path(output_dir)
        self._lock = threading.Lock()
        self._httpd: Optional[_ThreadingHTTPServer] = None
        self._thread: Optional[threading.Thread] = None

    @property
    def stream_url(self) -> str:
        assert self._httpd is not None
        addr, port = self._httpd.server_address[:2]
        return f"http://{addr}:{port}/stream"

    @property
    def ui_url(self) -> str:
        assert self._httpd is not None
        addr, port = self._httpd.server_address[:2]
        return f"http://{addr}:{port}/"

    def switch_session(self, new_session: TorrentVideoSession) -> None:
        with self._lock:
            old = self.active_session
            self.active_session = new_session
            self.store = new_session.store
            if old is not None and old is not new_session:
                threading.Thread(target=old.close, daemon=True).start()

    def start(self) -> str:
        outer = self

        class Handler(http.server.BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, format: str, *args: Any) -> None:
                pass

            def _send_json(self, status: int, data: Dict[str, Any]) -> None:
                raw = json.dumps(data).encode("utf-8")
                self.send_response(status)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(raw)))
                self.send_header("Connection", "close")
                self.close_connection = True
                self.end_headers()
                self.wfile.write(raw)

            def do_HEAD(self) -> None:
                self._handle_stream(send_body=False)

            def do_POST(self) -> None:
                if self.path.startswith("/api/upload-torrent"):
                    length = int(self.headers.get("Content-Length", "0"))
                    raw_bytes = self.rfile.read(length)
                    parsed_q = urllib.parse.parse_qs(urllib.parse.urlsplit(self.path).query)
                    fname = parsed_q.get("name", ["uploaded.torrent"])[0]
                    save_dir = outer.output_dir / "torrents"
                    save_dir.mkdir(parents=True, exist_ok=True)
                    target = save_dir / Path(fname).name
                    target.write_bytes(raw_bytes)
                    self._send_json(200, {"ok": True, "path": str(target)})
                    return

                if self.path.startswith("/api/start"):
                    length = int(self.headers.get("Content-Length", "0"))
                    body = json.loads(self.rfile.read(length).decode("utf-8"))
                    source = body.get("source", "").strip()
                    if not source:
                        source = get_default_fixture_magnet()
                    try:
                        sess = TorrentVideoSession(source, outer.output_dir, sliding_window_pieces=4)
                        sess.start_swarm()
                        outer.switch_session(sess)
                        self._send_json(200, {
                            "ok": True,
                            "info_hash": sess.metadata.info_hash.hex(),
                            "file_name": Path(sess.target_file.path).name,
                            "size": sess.target_file.length,
                            "output_path": str(sess.output_path),
                            "stream_url": "/stream",
                        })
                    except Exception as exc:
                        self._send_json(400, {"error": str(exc)})
                    return
                self._send_json(404, {"error": "Not found"})

            def do_GET(self) -> None:
                if self.path == "/" or self.path.startswith("/index.html"):
                    html_bytes = WEB_UI_HTML.encode("utf-8")
                    self.send_response(200)
                    self.send_header("Content-Type", "text/html; charset=utf-8")
                    self.send_header("Content-Length", str(len(html_bytes)))
                    self.send_header("Connection", "close")
                    self.close_connection = True
                    self.end_headers()
                    self.wfile.write(html_bytes)
                    return

                if self.path.startswith("/api/fixture-magnet"):
                    magnet = get_default_fixture_magnet()
                    self._send_json(200, {"magnet": magnet})
                    return

                if self.path.startswith("/status"):
                    store = outer.store
                    sess = outer.active_session
                    if store is None:
                        self._send_json(200, {"active": False, "progress": 0.0, "complete": False, "size": 0})
                        return
                    snap = store.piece_states_snapshot()
                    snap["active"] = True
                    if sess is not None:
                        snap["info_hash"] = sess.metadata.info_hash.hex()
                        snap["file_name"] = Path(sess.target_file.path).name
                        snap["output_path"] = str(sess.output_path)
                    self._send_json(200, snap)
                    return

                if self.path.startswith("/download"):
                    self._handle_stream(send_body=True, as_attachment=True)
                    return

                self._handle_stream(send_body=True, as_attachment=False)

            def _handle_stream(self, send_body: bool, as_attachment: bool = False) -> None:
                store = outer.store
                if store is None:
                    self.send_response(404, "No active torrent session")
                    self.send_header("Content-Length", "0")
                    self.send_header("Connection", "close")
                    self.close_connection = True
                    self.end_headers()
                    return

                total_size = store.target_file.length
                range_header = self.headers.get("Range")

                start_byte = 0
                end_byte = total_size - 1
                is_partial = False

                if range_header and range_header.startswith("bytes=") and not as_attachment:
                    is_partial = True
                    spec = range_header[len("bytes="):].strip().split(",")[0]
                    start_str, _, end_str = spec.partition("-")
                    if start_str == "" and end_str:
                        suffix_len = int(end_str)
                        start_byte = max(0, total_size - suffix_len)
                        end_byte = total_size - 1
                    else:
                        start_byte = int(start_str) if start_str else 0
                        end_byte = int(end_str) if end_str else (total_size - 1)
                    end_byte = min(end_byte, total_size - 1)

                if start_byte < 0 or start_byte >= total_size or start_byte > end_byte:
                    self.send_response(416, "Requested Range Not Satisfiable")
                    self.send_header("Content-Range", f"bytes */{total_size}")
                    self.send_header("Content-Length", "0")
                    self.send_header("Connection", "close")
                    self.close_connection = True
                    self.end_headers()
                    return

                content_length = (end_byte - start_byte) + 1
                if is_partial:
                    self.send_response(206, "Partial Content")
                    self.send_header("Content-Range", f"bytes {start_byte}-{end_byte}/{total_size}")
                else:
                    self.send_response(200, "OK")

                fname = Path(store.target_file.path).name
                self.send_header("Content-Type", "video/mp4")
                self.send_header("Accept-Ranges", "bytes")
                self.send_header("Content-Length", str(content_length))
                self.send_header("Connection", "close")
                self.close_connection = True
                if as_attachment:
                    self.send_header("Content-Disposition", f'attachment; filename="{fname}"')
                self.end_headers()

                if not send_body:
                    return

                cursor = start_byte
                while cursor <= end_byte:
                    to_read = min(outer.stream_chunk_size, (end_byte - cursor) + 1)
                    chunk = store.read_video_bytes(cursor, to_read, timeout=30.0)
                    if not chunk:
                        break
                    try:
                        self.wfile.write(chunk)
                        self.wfile.flush()
                    except (BrokenPipeError, ConnectionResetError, ConnectionAbortedError, OSError):
                        break
                    cursor += len(chunk)

        self._httpd = _ThreadingHTTPServer((self.host, self.port), Handler)
        self._thread = threading.Thread(target=self._httpd.serve_forever, daemon=True)
        self._thread.start()
        return self.stream_url

    def stop(self) -> None:
        if self._httpd is not None:
            self._httpd.shutdown()
            self._httpd.server_close()
            self._httpd = None


# ============================================================================
# 9. CLI & Web UI Entrypoint
# ============================================================================

def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Download or HTTP-Range stream any size video from a Magnet link or .torrent file."
    )
    parser.add_argument(
        "mode",
        nargs="?",
        default="ui",
        choices=["ui", "stream", "download"],
        help="Operation mode: 'ui' (Web Dashboard), 'stream', or 'download' (default: ui)",
    )
    parser.add_argument(
        "torrent",
        nargs="?",
        default="",
        help="Magnet URI ('magnet:?xt=urn:btih:...') or path to .torrent file",
    )
    parser.add_argument(
        "-o", "--output-dir", default="./downloads", help="Directory to store sparse/downloaded video"
    )
    parser.add_argument(
        "--peer",
        action="append",
        default=[],
        help="Optional explicit peer in host:port format (can be specified multiple times)",
    )
    parser.add_argument("--port", type=int, default=8080, help="HTTP Web UI & stream port (default: 8080)")
    args = parser.parse_args(argv)

    explicit_peers: List[Tuple[str, int]] = []
    for p in args.peer:
        h, _, pt = p.rpartition(":")
        explicit_peers.append((h, int(pt)))

    if args.mode == "ui":
        server = VideoStreamServer(host="127.0.0.1", port=args.port, output_dir=args.output_dir)
        server.start()
        fixture_magnet = get_default_fixture_magnet()
        if args.torrent:
            sess = TorrentVideoSession(args.torrent, args.output_dir, peers=explicit_peers)
            sess.start_swarm()
            server.switch_session(sess)
        print(f"Web UI running at: {server.ui_url}")
        print(f"Test Fixture Magnet Link ready:\n  {fixture_magnet}")
        print("Open http://127.0.0.1:%d in your browser to paste magnet links and stream/download." % args.port)
        print("Press Ctrl+C to stop.")
        try:
            while True:
                time.sleep(0.5)
        except KeyboardInterrupt:
            print("\nShutting down Web UI.")
        finally:
            server.stop()
        return 0

    target_source = args.torrent or get_default_fixture_magnet()
    session = TorrentVideoSession(target_source, args.output_dir, peers=explicit_peers)
    try:
        session.start_swarm()
        if args.mode == "stream":
            url = session.start_http_stream(port=args.port)
            print(f"Web UI Dashboard : http://127.0.0.1:{args.port}/")
            print(f"Direct Stream URL: {url}")
            print(f"Streaming '{session.target_file.path}' ({session.target_file.length} bytes)")
            print("Press Ctrl+C to stop streaming.")
            try:
                while True:
                    time.sleep(0.5)
            except KeyboardInterrupt:
                print("\nStopping stream server.")
        else:
            print(f"Downloading '{session.target_file.path}' ({session.target_file.length} bytes)...")
            ok = session.wait_until_complete(timeout=300.0)
            if not ok:
                print("Download timed out.", file=sys.stderr)
                return 1
            print(f"Saved verified video to: {session.output_path}")
        return 0
    finally:
        session.close()


if __name__ == "__main__":
    raise SystemExit(main())
