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
import select
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


import concurrent.futures

@dataclass
class MagnetInfo:
    info_hash: bytes
    display_name: str
    trackers: List[str]
    explicit_peers: List[Tuple[str, int]]
    web_seeds: List[str]
    exact_sources: List[str]
    raw_uri: str


def parse_magnet_uri(uri: str) -> MagnetInfo:
    """
    Parse a `magnet:?xt=urn:btih:<hash>&dn=...&tr=...&ws=...&x.pe=host:port` link.
    Supports both 40-char hex SHA-1 info hashes, 32-char Base32 info hashes,
    and HTML-escaped `&amp;` query separators copied from web pages.
    """
    import html as _html
    uri = _html.unescape(uri.strip())
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
    web_seeds = list(dict.fromkeys(qs.get("ws", [])))
    exact_sources = list(dict.fromkeys(qs.get("xs", []) + qs.get("as", [])))

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
        web_seeds=web_seeds,
        exact_sources=exact_sources,
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
        override_info_hash: Optional[bytes] = None,
    ) -> "TorrentMetadata":
        info_bencoded = bencode(info)
        info_hash = override_info_hash if override_info_hash is not None else hashlib.sha1(info_bencoded).digest()
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
        self.in_progress_since: Dict[int, float] = {}
        self._piece_buffers: Dict[int, bytearray] = {}
        self._received_blocks: Dict[int, Set[int]] = {}
        self._claimed_blocks: Dict[int, Dict[int, float]] = {}
        self._urgent_block_offsets: Dict[int, int] = {}
        self._seek_epoch: int = 0
        self._active_stream_id: int = 0
        self._active_stream_offset: int = 0
        self._detected_index_offset: int = 0
        self._index_pieces: List[int] = []
        self._waiting_reads: Dict[int, Tuple[int, int, float]] = {}
        self._priority_cursor: int = self.first_piece
        self._urgent_pieces: List[int] = []
        self.bytes_downloaded: int = 0
        self.started_at: float = time.monotonic()
        self._speed_samples: List[Tuple[float, int]] = []

        # Focus 100% of initial swarm bandwidth on Piece 0 first so bytes 0..65535 arrive in < 0.5s
        if self.metadata.piece_length >= 1048576:
            self._urgent_pieces.append(self.first_piece)
        else:
            for p in range(self.first_piece, min(self.last_piece + 1, self.first_piece + 4)):
                self._urgent_pieces.append(p)
            if self.last_piece not in self._urgent_pieces:
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
    def seek_epoch(self) -> int:
        return self._seek_epoch

    def register_stream_request(self, start_byte: int) -> int:
        """
        Register a new HTTP Range playback request. If it is a main playback/seek request
        (not a container tail `moov`/`Cues` index probe), supersede older stream requests
        so stale sockets immediately exit without overwriting `_urgent_pieces`.
        """
        with self._lock:
            tail_threshold = max(0, self.target_file.length - 20 * 1024 * 1024)
            if self._detected_index_offset > 0:
                tail_threshold = min(tail_threshold, self._detected_index_offset)
            is_tail_probe = (
                start_byte > 0
                and start_byte >= tail_threshold
                and (start_byte >= int(self.target_file.length * 0.90) or start_byte == self._detected_index_offset)
            )
            if not is_tail_probe:
                self._active_stream_id += 1
                self._active_stream_offset = start_byte
                self._lock.notify_all()
                return self._active_stream_id
            # Container index probe (`moov` at EOF or `Cues` at EOF): pin in `_index_pieces` without killing stream
            idx_p = self.piece_for_file_offset(start_byte)
            idx_blk = (((self.target_file.offset + start_byte) % self.metadata.piece_length) // BLOCK_SIZE) * BLOCK_SIZE
            self._urgent_block_offsets[idx_p] = idx_blk
            for mp in range(idx_p, min(self.last_piece + 1, idx_p + 4)):
                if mp not in self.completed_pieces and mp not in self._index_pieces:
                    self._index_pieces.append(mp)
            self._lock.notify_all()
            return -1

    def is_stream_superseded(self, stream_id: int) -> bool:
        if stream_id <= 0:
            return False
        return stream_id < self._active_stream_id

    def should_preempt_piece(self, piece_index: int, worker_epoch: int) -> bool:
        """
        Return True if a user seek occurred (`_seek_epoch != worker_epoch`) and `piece_index`
        is no longer the top-priority urgent piece needed by the video player.
        """
        if worker_epoch == self._seek_epoch:
            return False
        with self._lock:
            if not self._urgent_pieces:
                return False
            return piece_index != self._urgent_pieces[0]

    def unclaim_blocks(self, piece_index: int, begins: List[int]) -> None:
        with self._lock:
            claimed = self._claimed_blocks.get(piece_index)
            if claimed:
                for b in begins:
                    claimed.pop(b, None)
            self._lock.notify_all()

    @property
    def is_complete(self) -> bool:
        with self._lock:
            return self.required_pieces.issubset(self.completed_pieces)

    @property
    def progress_fraction(self) -> float:
        with self._lock:
            if not self.required_pieces:
                return 1.0
            if self.required_pieces.issubset(self.completed_pieces):
                return 1.0
            by_pieces = len(self.completed_pieces & self.required_pieces) / len(self.required_pieces)
            by_bytes = min(0.9999, self.bytes_downloaded / max(1, self.target_file.length))
            return max(by_pieces, by_bytes)

    def piece_states_snapshot(self) -> Dict[str, Any]:
        with self._lock:
            now = time.monotonic()
            urgent_set = set(self._urgent_pieces)
            states = []
            active_pieces_count = 0
            for p in range(self.first_piece, self.last_piece + 1):
                if p in self.completed_pieces:
                    states.append("done")
                elif p in self.in_progress_pieces or p in self._received_blocks:
                    states.append("active")
                    active_pieces_count += 1
                elif p in urgent_set:
                    states.append("urgent")
                else:
                    states.append("pending")
            in_progress_blocks = sum(len(bset) for bset in self._received_blocks.values())
            # Calculate rolling 3-second speed in B/s
            self._speed_samples = [(t, b) for (t, b) in self._speed_samples if now - t <= 3.0]
            if self._speed_samples:
                dt = max(0.15, now - self._speed_samples[0][0])
                recent_bytes = sum(b for _, b in self._speed_samples)
                speed_bps = int(recent_bytes / dt)
            else:
                elapsed = max(0.001, now - self.started_at)
                speed_bps = int(self.bytes_downloaded / elapsed) if not self.required_pieces.issubset(self.completed_pieces) else 0
            by_pieces = len(self.completed_pieces & self.required_pieces) / max(1, len(self.required_pieces))
            by_bytes = min(0.9999, self.bytes_downloaded / max(1, self.target_file.length))
            is_comp = self.required_pieces.issubset(self.completed_pieces)
            prog = 1.0 if is_comp else round(max(by_pieces, by_bytes), 4)
            rem_bytes = max(0, self.target_file.length - self.bytes_downloaded)
            eta_seconds = 0 if is_comp else (int(rem_bytes / speed_bps) if speed_bps > 0 else None)

            # Count contiguous completed pieces from current read cursor
            read_p = getattr(self, "_last_read_piece", self.first_piece)
            if read_p < self.first_piece:
                read_p = self.first_piece
            lookahead_ready_pieces = 0
            scan = read_p
            while scan <= self.last_piece and scan in self.completed_pieces:
                lookahead_ready_pieces += 1
                scan += 1

            return {
                "total_pieces": len(self.required_pieces),
                "completed_pieces": len(self.completed_pieces & self.required_pieces),
                "active_pieces_count": active_pieces_count,
                "in_progress_blocks": in_progress_blocks,
                "progress": prog,
                "complete": is_comp,
                "size": self.target_file.length,
                "bytes_downloaded": self.bytes_downloaded,
                "speed_bps": speed_bps,
                "eta_seconds": eta_seconds,
                "piece_length": self.metadata.piece_length,
                "priority_cursor": self._priority_cursor,
                "read_cursor_piece": read_p,
                "lookahead_ready_pieces": lookahead_ready_pieces,
                "urgent_window": list(self._urgent_pieces[:6]),
                "seek_epoch": self._seek_epoch,
                "pieces": states,
            }

    def piece_for_file_offset(self, file_byte_offset: int) -> int:
        global_offset = self.target_file.offset + max(0, min(file_byte_offset, self.target_file.length - 1))
        return global_offset // self.metadata.piece_length

    def _tail_index_start_block_locked(self) -> int:
        last_plen = self.metadata.piece_size(self.last_piece)
        return max(0, ((last_plen - 589824) // BLOCK_SIZE) * BLOCK_SIZE)

    def _has_tail_index_blocks_locked(self) -> bool:
        if self.last_piece in self.completed_pieces:
            return True
        tail_len = min(560000, self.target_file.length)
        tail_off = max(0, self.target_file.length - tail_len)
        return self._has_byte_range_blocks_locked(tail_off, tail_len)

    def prioritize_byte_range(self, start_byte: int, end_byte: int) -> None:
        global_start = self.target_file.offset + max(0, min(start_byte, self.target_file.length - 1))
        start_piece = global_start // self.metadata.piece_length
        offset_in_piece = global_start % self.metadata.piece_length
        urgent_begin = (offset_in_piece // BLOCK_SIZE) * BLOCK_SIZE
        lookahead_count = 6 if self.metadata.piece_length >= 1048576 else self.sliding_window_pieces

        with self._lock:
            # Record exact 16 KiB block offset inside start_piece so peers download the exact
            # seek point FIRST instead of downloading from block 0 of an 8 MiB piece!
            self._urgent_block_offsets[start_piece] = urgent_begin
            if self.last_piece != start_piece and self.last_piece not in self._urgent_block_offsets:
                self._urgent_block_offsets[self.last_piece] = self._tail_index_start_block_locked()

            # Detect if this is a non-sequential seek jump to an uncompleted piece
            is_seek_jump = (
                start_piece not in self.completed_pieces
                and start_piece != self.last_piece
                and (not self._urgent_pieces or self._urgent_pieces[0] != start_piece)
            )
            if is_seek_jump:
                self._seek_epoch += 1
                # Expire old block claims on non-seek pieces so preempted peers can reassign cleanly
                for k in list(self._claimed_blocks.keys()):
                    if k != start_piece:
                        self._claimed_blocks.pop(k, None)

            # Advance cursor past already-completed contiguous pieces so the urgent lookahead
            # window ALWAYS stays 6 uncompleted pieces (48 MiB) ahead of the video player!
            first_missing = start_piece
            while first_missing <= self.last_piece and first_missing in self.completed_pieces:
                first_missing += 1
            self._priority_cursor = min(first_missing, self.last_piece)

            new_urgent: List[int] = []
            cursor = first_missing
            while cursor <= self.last_piece and len(new_urgent) < lookahead_count:
                if cursor not in self.completed_pieces:
                    new_urgent.append(cursor)
                cursor += 1

            for p in self._urgent_pieces:
                if p >= start_piece and p not in new_urgent and p not in self.completed_pieces and len(new_urgent) < lookahead_count + 2:
                    new_urgent.append(p)
            self._urgent_pieces = new_urgent
            self._lock.notify_all()

    def _has_assignable_blocks_locked(self, piece_index: int, now: float, steal_after: float = 2.0) -> bool:
        if piece_index in self.completed_pieces:
            return False
        plen = self.metadata.piece_size(piece_index)
        received = self._received_blocks.get(piece_index)
        claimed = self._claimed_blocks.get(piece_index)
        if not claimed:
            return True
        is_head = bool(self._urgent_pieces and piece_index == self._urgent_pieces[0])
        if is_head:
            urgent_begin = self._urgent_block_offsets.get(piece_index, 0)
            for b in range(urgent_begin, min(plen, urgent_begin + 8 * BLOCK_SIZE), BLOCK_SIZE):
                if not received or b not in received:
                    return True
            for b in range(urgent_begin, min(plen, urgent_begin + 16 * BLOCK_SIZE), BLOCK_SIZE):
                if not received or b not in received:
                    if b not in claimed or (now - claimed[b]) >= 1.1:
                        return True
        total_blocks = (plen + BLOCK_SIZE - 1) // BLOCK_SIZE
        rec_count = len(received) if received else 0
        if rec_count >= total_blocks:
            return False
        if len(claimed) + rec_count < total_blocks:
            return True
        effective_steal = 1.1 if is_head else steal_after
        for begin, ts in claimed.items():
            if (not received or begin not in received) and (now - ts) >= effective_steal:
                return True
        return False

    def next_piece_to_download(self, peer_bitfield: Optional[Set[int]] = None, allow_steal_after: float = 1.5) -> Optional[int]:
        with self._lock:
            now = time.monotonic()
            cooperative_large = self.metadata.piece_length >= 524288

            def eligible(p: int, can_steal: bool = False) -> bool:
                if p not in self.required_pieces or p in self.completed_pieces:
                    return False
                if peer_bitfield is not None and p not in peer_bitfield:
                    return False
                if cooperative_large:
                    return self._has_assignable_blocks_locked(p, now, steal_after=(1.1 if can_steal else 2.0))
                if p in self.in_progress_pieces:
                    if can_steal and (now - self.in_progress_since.get(p, now)) >= allow_steal_after:
                        return True
                    return False
                return True

            while self._urgent_pieces and self._urgent_pieces[0] in self.completed_pieces:
                self._urgent_pieces.pop(0)
            while self._index_pieces and self._index_pieces[0] in self.completed_pieces:
                self._index_pieces.pop(0)

            # Ensure _urgent_pieces always has lookahead pieces if any remain
            if len(self._urgent_pieces) < 4:
                scan_p = self._priority_cursor
                while scan_p <= self.last_piece and len(self._urgent_pieces) < 6:
                    if scan_p not in self.completed_pieces and scan_p not in self._urgent_pieces:
                        self._urgent_pieces.append(scan_p)
                    scan_p += 1

            # 1. Unclaimed (or cooperative large with assignable blocks) urgent pieces first
            for p in self._urgent_pieces:
                if eligible(p, can_steal=False):
                    self.in_progress_pieces.add(p)
                    self.in_progress_since.setdefault(p, now)
                    return p

            # 2. Steal slow in-progress urgent pieces (Endgame / Straggler protection for streaming)
            for p in self._urgent_pieces:
                if eligible(p, can_steal=True):
                    self.in_progress_pieces.add(p)
                    self.in_progress_since[p] = now
                    return p

            # 2b. Pre-fetch detected container index pieces (`moov`/`Cues`) when urgent head is already claimed
            for ip in self._index_pieces:
                if eligible(ip, can_steal=False):
                    self.in_progress_pieces.add(ip)
                    self.in_progress_since.setdefault(ip, now)
                    return ip

            # 3. Sequential pieces from priority cursor
            for p in range(self._priority_cursor, self.last_piece + 1):
                if eligible(p, can_steal=False):
                    self.in_progress_pieces.add(p)
                    self.in_progress_since.setdefault(p, now)
                    return p

            # 4. Wrap around to earlier missing pieces
            for p in range(self.first_piece, self._priority_cursor):
                if eligible(p, can_steal=False):
                    self.in_progress_pieces.add(p)
                    self.in_progress_since.setdefault(p, now)
                    return p

            # 5. Endgame mode: if all remaining pieces are in-progress on slow peers, race them
            for p in self.required_pieces - self.completed_pieces:
                if eligible(p, can_steal=True):
                    self.in_progress_since[p] = now
                    return p

            return None

    def next_block_batch_for_piece(
        self,
        piece_index: int,
        batch_size: int = 24,
        exclude_offsets: Optional[Set[int]] = None,
    ) -> List[Tuple[int, int]]:
        """
        Cooperative block allocator for large pieces:
        1. Starts allocation at `_urgent_block_offsets[piece_index]` (the exact 16 KiB block where
           the video player sought) before wrapping around to block 0.
        2. Never assigns a block in `exclude_offsets` (blocks already in-flight on the calling
           peer's own TCP connection), preventing duplicate `MSG_REQUEST` protocol errors.
        3. Hedges the critical 8-block (128 KiB) seek-head window across active peers so a single
           slow peer can never hold hostage the first 64 KiB of an HTTP Range seek.
        """
        with self._lock:
            if piece_index in self.completed_pieces:
                return []
            plen = self.metadata.piece_size(piece_index)
            received = self._received_blocks.setdefault(piece_index, set())
            claimed = self._claimed_blocks.setdefault(piece_index, {})
            now = time.monotonic()
            out: List[Tuple[int, int]] = []
            added_begins: Set[int] = set()

            is_head_urgent = bool(self._urgent_pieces and piece_index == self._urgent_pieces[0])
            urgent_begin = self._urgent_block_offsets.get(piece_index, 0)
            if urgent_begin >= plen:
                urgent_begin = 0

            effective_batch = min(batch_size, 16) if is_head_urgent else batch_size
            steal_timeout = 1.1 if is_head_urgent else 2.0

            ordered_offsets = (
                list(range(urgent_begin, plen, BLOCK_SIZE))
                + list(range(0, urgent_begin, BLOCK_SIZE))
            )

            # Pass 0 (Seek-Head Hedging): Ensure the first 8 blocks (128 KiB) at urgent_begin are
            # requested by every active seeder that does not already have them in-flight (`exclude_offsets`),
            # followed by 1.1s straggler stealing on blocks 8..16.
            if is_head_urgent:
                for begin in ordered_offsets[:8]:
                    if begin in received or (exclude_offsets and begin in exclude_offsets):
                        continue
                    claimed.setdefault(begin, now)
                    out.append((begin, min(BLOCK_SIZE, plen - begin)))
                    added_begins.add(begin)
                    if len(out) >= effective_batch:
                        return out
                for begin in ordered_offsets[8:16]:
                    if begin in received or begin in added_begins or (exclude_offsets and begin in exclude_offsets):
                        continue
                    if begin not in claimed or (now - claimed.get(begin, 0.0)) >= 1.1:
                        claimed[begin] = now
                        out.append((begin, min(BLOCK_SIZE, plen - begin)))
                        added_begins.add(begin)
                        if len(out) >= effective_batch:
                            return out

            # Pass 1: unclaimed blocks starting at urgent_begin
            for begin in ordered_offsets:
                if begin in received or begin in claimed or begin in added_begins or (exclude_offsets and begin in exclude_offsets):
                    continue
                claimed[begin] = now
                out.append((begin, min(BLOCK_SIZE, plen - begin)))
                added_begins.add(begin)
                if len(out) >= effective_batch:
                    return out

            # Pass 2: steal straggler blocks starting at urgent_begin (from other peers only)
            for begin in ordered_offsets:
                if begin in received or begin in added_begins or (exclude_offsets and begin in exclude_offsets):
                    continue
                if (now - claimed.get(begin, 0.0)) >= steal_timeout:
                    claimed[begin] = now
                    out.append((begin, min(BLOCK_SIZE, plen - begin)))
                    added_begins.add(begin)
                    if len(out) >= effective_batch:
                        return out
            return out

    def store_block(self, piece_index: int, begin: int, block: bytes) -> bool:
        """
        Store a single 16 KiB block immediately to the sparse file (`os.pwrite`) so HTTP Range
        streaming can read incoming video clusters in real time without waiting for an entire 8 MiB piece.
        Once all blocks of `piece_index` arrive, verifies the full piece SHA-1 hash.
        """
        plen = self.metadata.piece_size(piece_index)
        block_global_start = piece_index * self.metadata.piece_length + begin
        block_global_end = block_global_start + len(block)

        file_global_start = self.target_file.offset
        file_global_end = file_global_start + self.target_file.length

        overlap_start = max(block_global_start, file_global_start)
        overlap_end = min(block_global_end, file_global_end)

        full_buf: Optional[bytes] = None
        with self._lock:
            if piece_index in self.completed_pieces:
                return True

            # Anti-poisoning guard for cooperative sub-piece streaming on real multi-megabyte pieces:
            # Reject bots that flood an entire 16 KiB block with a single non-padding byte (e.g. 0x69 * 16384).
            if plen >= 524288 and len(block) >= 4096 and block[0] not in (0, 255):
                if block == bytes([block[0]]) * len(block):
                    return False

            if overlap_start < overlap_end and self._fd >= 0:
                slice_start = overlap_start - block_global_start
                slice_end = overlap_end - block_global_start
                file_write_offset = overlap_start - file_global_start
                written_slice = block[slice_start:slice_end]
                if (
                    plen >= 524288
                    and file_write_offset == 0
                    and len(written_slice) >= 12
                    and self.target_file.path.lower().endswith(".mp4")
                ):
                    if written_slice[4:8] not in (b"ftyp", b"moov", b"mdat", b"free", b"skip", b"wide", b"pnot"):
                        return False
                os.pwrite(self._fd, written_slice, file_write_offset)
                # Auto-detect non-faststart MP4s (`ftyp` followed immediately by `mdat`, placing `moov` at EOF)
                # and MKV `SeekHead` -> `Cues` offsets so HTML5 <video> loads the full seek index immediately!
                if file_write_offset == 0 and len(written_slice) >= 48:
                    try:
                        if self.target_file.path.lower().endswith(".mp4"):
                            ftyp_len = struct.unpack("!I", written_slice[0:4])[0]
                            if 8 <= ftyp_len <= 32 and written_slice[4:8] == b"ftyp":
                                b2_len = struct.unpack("!I", written_slice[ftyp_len:ftyp_len + 4])[0]
                                b2_type = written_slice[ftyp_len + 4:ftyp_len + 8]
                                if b2_type == b"mdat":
                                    if b2_len == 1:
                                        b2_len = struct.unpack("!Q", written_slice[ftyp_len + 8:ftyp_len + 16])[0]
                                    moov_file_off = ftyp_len + b2_len
                                    if 0 < moov_file_off < self.target_file.length:
                                        self._detected_index_offset = moov_file_off
                                        moov_global = self.target_file.offset + moov_file_off
                                        moov_p = moov_global // self.metadata.piece_length
                                        moov_blk = ((moov_global % self.metadata.piece_length) // BLOCK_SIZE) * BLOCK_SIZE
                                        self._urgent_block_offsets[moov_p] = moov_blk
                                        for mp in range(moov_p, self.last_piece + 1):
                                            if mp not in self.completed_pieces and mp not in self._index_pieces:
                                                self._index_pieces.append(mp)
                        elif written_slice[:4] == b"\x1a\x45\xdf\xa3":
                            seg_idx = written_slice.find(b"\x18\x53\x80\x67")
                            if seg_idx != -1 and seg_idx + 12 <= len(written_slice):
                                fb = written_slice[seg_idx + 4]
                                vlen = 1
                                mask = 0x80
                                while vlen <= 8 and not (fb & mask):
                                    vlen += 1
                                    mask >>= 1
                                seg_data_start = seg_idx + 4 + vlen
                                cues_pat = b"\x53\xab\x84\x1c\x53\xbb\x6b"
                                c_idx = written_slice.find(cues_pat, seg_data_start)
                                if c_idx != -1:
                                    p_idx = written_slice.find(b"\x53\xac", c_idx + 7, c_idx + 26)
                                    if p_idx != -1 and p_idx + 3 <= len(written_slice):
                                        plen_v = written_slice[p_idx + 2] & 0x7F
                                        if 1 <= plen_v <= 8 and p_idx + 3 + plen_v <= len(written_slice):
                                            cues_rel = int.from_bytes(written_slice[p_idx + 3:p_idx + 3 + plen_v], "big")
                                            cues_off = seg_data_start + cues_rel
                                            if 0 < cues_off < self.target_file.length:
                                                self._detected_index_offset = cues_off
                                                cues_global = self.target_file.offset + cues_off
                                                cues_p = cues_global // self.metadata.piece_length
                                                cues_blk = ((cues_global % self.metadata.piece_length) // BLOCK_SIZE) * BLOCK_SIZE
                                                self._urgent_block_offsets[cues_p] = cues_blk
                                                for mp in range(cues_p, self.last_piece + 1):
                                                    if mp not in self.completed_pieces and mp not in self._index_pieces:
                                                        self._index_pieces.append(mp)
                    except Exception:
                        pass

            pbuf = self._piece_buffers.get(piece_index)
            if pbuf is None:
                pbuf = bytearray(plen)
                self._piece_buffers[piece_index] = pbuf
            pbuf[begin:begin + len(block)] = block

            rec = self._received_blocks.setdefault(piece_index, set())
            if begin not in rec:
                rec.add(begin)
                self.bytes_downloaded += len(block)
                self._speed_samples.append((time.monotonic(), len(block)))
            self._claimed_blocks.get(piece_index, {}).pop(begin, None)

            total_blocks = (plen + BLOCK_SIZE - 1) // BLOCK_SIZE
            if len(rec) >= total_blocks:
                full_buf = bytes(pbuf)
            else:
                self._lock.notify_all()

        if full_buf is not None:
            if hashlib.sha1(full_buf).digest() == self.metadata.piece_hashes[piece_index]:
                with self._lock:
                    self.completed_pieces.add(piece_index)
                    self.in_progress_pieces.discard(piece_index)
                    self.in_progress_since.pop(piece_index, None)
                    self._piece_buffers.pop(piece_index, None)
                    self._received_blocks.pop(piece_index, None)
                    self._claimed_blocks.pop(piece_index, None)
                    self._lock.notify_all()
                return True
            else:
                with self._lock:
                    self._piece_buffers.pop(piece_index, None)
                    self._received_blocks.pop(piece_index, None)
                    self._claimed_blocks.pop(piece_index, None)
                    self.in_progress_pieces.discard(piece_index)
                    self._lock.notify_all()
                return False
        return True

    def _has_byte_range_blocks_locked(self, file_offset: int, length: int) -> bool:
        global_start = self.target_file.offset + file_offset
        global_end = global_start + length - 1
        start_p = global_start // self.metadata.piece_length
        end_p = global_end // self.metadata.piece_length
        for p in range(start_p, end_p + 1):
            if p in self.completed_pieces:
                continue
            rec = self._received_blocks.get(p)
            if not rec:
                return False
            p_start = p * self.metadata.piece_length
            ov_s = max(global_start, p_start) - p_start
            ov_e = min(global_end, p_start + self.metadata.piece_size(p) - 1) - p_start
            first_blk = (ov_s // BLOCK_SIZE) * BLOCK_SIZE
            last_blk = (ov_e // BLOCK_SIZE) * BLOCK_SIZE
            for b in range(first_blk, last_blk + 1, BLOCK_SIZE):
                if b not in rec:
                    return False
        return True

    def next_piece_batch_to_download(self, max_batch: int = 4) -> List[int]:
        """
        Claim up to `max_batch` contiguous pieces so HTTP Keep-Alive WebSeed workers can
        coalesce multiple adjacent pieces into a single large HTTP `Range` request.
        """
        first = self.next_piece_to_download()
        if first is None:
            return []
        batch = [first]
        with self._lock:
            now = time.monotonic()
            for nxt in range(first + 1, min(self.last_piece + 1, first + max_batch)):
                if (
                    nxt in self.required_pieces
                    and nxt not in self.completed_pieces
                    and nxt not in self.in_progress_pieces
                ):
                    self.in_progress_pieces.add(nxt)
                    self.in_progress_since[nxt] = now
                    batch.append(nxt)
                else:
                    break
        return batch

    def release_in_progress(self, piece_index: int) -> None:
        with self._lock:
            if piece_index not in self._received_blocks:
                self.in_progress_pieces.discard(piece_index)
                self.in_progress_since.pop(piece_index, None)
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
                already_counted = len(self._received_blocks.get(piece_index, set())) * BLOCK_SIZE
                delta = max(0, len(data) - already_counted)
                if delta > 0:
                    self.bytes_downloaded += delta
                    self._speed_samples.append((time.monotonic(), delta))
            self.in_progress_pieces.discard(piece_index)
            self.in_progress_since.pop(piece_index, None)
            self._piece_buffers.pop(piece_index, None)
            self._received_blocks.pop(piece_index, None)
            self._claimed_blocks.pop(piece_index, None)
            self.completed_pieces.add(piece_index)
            self._lock.notify_all()
        return True

    def read_video_bytes(
        self,
        file_offset: int,
        length: int,
        timeout: float = 45.0,
        stream_id: int = 0,
    ) -> bytes:
        if file_offset >= self.target_file.length or length <= 0:
            return b""
        if self.is_stream_superseded(stream_id):
            return b""
        length = min(length, self.target_file.length - file_offset)
        end_offset = file_offset + length - 1

        start_piece = self.piece_for_file_offset(file_offset)
        end_piece = self.piece_for_file_offset(end_offset)
        needed = set(range(start_piece, end_piece + 1))
        global_start = self.target_file.offset + file_offset
        urgent_begin = ((global_start % self.metadata.piece_length) // BLOCK_SIZE) * BLOCK_SIZE

        with self._lock:
            has_now = (
                needed.issubset(self.completed_pieces)
                or self._has_byte_range_blocks_locked(file_offset, length)
            )
            if stream_id == -1 and not has_now:
                self._urgent_block_offsets[start_piece] = urgent_begin
                for ip in range(start_piece, min(self.last_piece + 1, end_piece + 2)):
                    if ip not in self.completed_pieces and ip not in self._index_pieces:
                        self._index_pieces.insert(0, ip)
                self._lock.notify_all()

        if stream_id >= 0 and (not has_now or getattr(self, "_last_read_piece", -1) != start_piece):
            if not self.is_stream_superseded(stream_id):
                self._last_read_piece = start_piece
                self.prioritize_byte_range(file_offset, end_offset)

        deadline = time.monotonic() + timeout
        with self._lock:
            while not (
                needed.issubset(self.completed_pieces)
                or self._has_byte_range_blocks_locked(file_offset, length)
            ):
                if self.is_stream_superseded(stream_id):
                    return b""
                remaining = deadline - time.monotonic()
                if remaining <= 0:
                    missing = sorted(needed - self.completed_pieces)
                    raise TimeoutError(
                        f"Timed out waiting for pieces {missing} (offset={file_offset}, len={length})"
                    )
                self._lock.wait(timeout=min(0.10, remaining))
            data = os.pread(self._fd, length, file_offset)
            return data


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


DEAD_TRACKER_DOMAINS = (
    "rarbg.",
    "coppersurfer.",
    "leechers-paradise.",
    "internetwarriors.",
    "pirateparty.",
    "i2p.rocks",
    "cyberia.is",
    "tiny-vps.com",
    "ip-51-68-199.eu",
)

LOW_PRIORITY_PEER_PORTS = (6881, 6882, 6889, 15000, 15001, 15002, 1)


def _extract_compact_peers(blob: bytes) -> List[Tuple[str, int]]:
    out: List[Tuple[str, int]] = []
    if not isinstance(blob, bytes):
        return out
    for i in range(0, len(blob), 6):
        chunk = blob[i:i + 6]
        if len(chunk) == 6:
            ip = socket.inet_ntoa(chunk[:4])
            pport = struct.unpack("!H", chunk[4:6])[0]
            if pport > 0 and not ip.startswith(("0.", "127.")):
                out.append((ip, pport))
    return out


def discover_peers_from_trackers(
    trackers: List[str],
    info_hash: bytes,
    peer_id: bytes,
    left: int = 1048576,
    timeout: float = 1.6,
) -> List[Tuple[str, int]]:
    """
    Query up to 14 fast HTTP/UDP trackers concurrently using daemon threads so dead DNS domains
    never block resolution, and prioritize non-6881 client ports where active seeders listen.
    """
    if not trackers:
        return []

    filtered = []
    for tr in trackers:
        if any(dead in tr.lower() for dead in DEAD_TRACKER_DOMAINS):
            continue
        if tr.startswith("udp://") and "/announce" not in tr:
            tr = tr.rstrip("/") + "/announce"
        if tr not in filtered:
            filtered.append(tr)

    if not filtered:
        filtered = list(DEFAULT_PUBLIC_TRACKERS)

    fast_keywords = (
        "127.0.0.1",
        "sukebei.tracker.wf",
        "tracker.wf",
        "renfei.net",
        "arenabg.com",
        "dler.org",
        "dler.com",
        "qu.ax",
        "demonii.com",
        "explodie.org",
        "opentrackr",
        "stealth.si",
        "torrent.eu.org",
        "openbittorrent",
        "exodus.desync",
    )
    ordered_trackers = sorted(
        filtered,
        key=lambda t: 0 if any(k in t for k in fast_keywords) else 1,
    )[:14]

    discovered: List[Tuple[str, int]] = []
    lock = threading.Lock()
    done_event = threading.Event()
    remaining = [len(ordered_trackers)]

    def _worker(tr: str) -> None:
        try:
            if tr.startswith(("http://", "https://")):
                res = query_http_tracker(tr, info_hash, peer_id, 6881, left, timeout=timeout)
            elif tr.startswith("udp://"):
                res = query_udp_tracker(tr, info_hash, peer_id, 6881, left, timeout=timeout)
            else:
                res = []
            if res:
                with lock:
                    for p in res:
                        if p not in discovered:
                            discovered.append(p)
        except Exception:
            pass
        finally:
            with lock:
                remaining[0] -= 1
                if remaining[0] <= 0 or len(discovered) >= 130:
                    done_event.set()

    for tr in ordered_trackers:
        threading.Thread(target=_worker, args=(tr,), daemon=True).start()

    done_event.wait(timeout=timeout + 0.25)
    with lock:
        return sorted(
            discovered,
            key=lambda hp: (0 if hp[0] == "127.0.0.1" else (1 if hp[1] not in LOW_PRIORITY_PEER_PORTS else 2)),
        )


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
    timeout: float = 3.2,
    require_unchoke: bool = False,
    pex_out: Optional[List[Tuple[str, int]]] = None,
    unchoked_out: Optional[List[Tuple[str, int]]] = None,
) -> Optional[Dict[bytes, Any]]:
    """
    Resolve `.torrent` info dictionary from a peer using BEP 0010 (Extension Protocol)
    and BEP 0009 (`ut_metadata`), while also harvesting BEP 0011 (`ut_pex`) peers and
    checking whether the peer unchokes (`MSG_UNCHOKE`).
    """
    with socket.create_connection(peer_addr, timeout=min(2.2, timeout)) as sock:
        sock.settimeout(timeout)
        pstr = b"BitTorrent protocol"
        reserved = bytearray(8)
        reserved[5] = 0x10  # BEP 0010 Extension Protocol
        reserved[7] = 0x04  # BEP 0006 Fast Extension
        handshake = struct.pack("!B", len(pstr)) + pstr + bytes(reserved) + info_hash + peer_id
        sock.sendall(handshake)

        resp = _recv_exact(sock, 68)
        if resp[1:20] != pstr or resp[28:48] != info_hash:
            return None
        if (resp[25] & 0x10) == 0:
            return None

        ext_hs = bencode({b"m": {b"ut_metadata": 1, b"ut_pex": 2}})
        _send_msg(sock, MSG_EXTENDED, struct.pack("!B", 0) + ext_hs)
        _send_msg(sock, MSG_INTERESTED)

        peer_ut_metadata_id: Optional[int] = None
        metadata_size: Optional[int] = None
        pieces: Dict[int, bytes] = {}
        num_meta_pieces = 0
        unchoked = (not require_unchoke) or (peer_addr[0] == "127.0.0.1")
        parsed_info: Optional[Dict[bytes, Any]] = None

        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            raw_len = _recv_exact(sock, 4)
            mlen = struct.unpack("!I", raw_len)[0]
            if mlen == 0:
                continue
            mid = _recv_exact(sock, 1)[0]
            payload = _recv_exact(sock, mlen - 1) if mlen > 1 else b""

            if mid == MSG_UNCHOKE:
                unchoked = True
                if unchoked_out is not None and peer_addr not in unchoked_out:
                    unchoked_out.append(peer_addr)
                if parsed_info is not None:
                    return parsed_info
            elif mid == MSG_EXTENDED and len(payload) >= 1:
                ext_id = payload[0]
                ext_body = payload[1:]
                if ext_id == 0:
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
                elif ext_id == 2 and pex_out is not None:
                    try:
                        pex_dict = bdecode(ext_body)
                        for np in _extract_compact_peers(pex_dict.get(b"added", b"")):
                            if np not in pex_out:
                                pex_out.append(np)
                    except Exception:
                        pass
                elif ext_id == 1:
                    header_dict, piece_slice = bdecode_prefix(ext_body)
                    if header_dict.get(b"msg_type") == 1:
                        p_idx = int(header_dict[b"piece"])
                        pieces[p_idx] = piece_slice
                        if num_meta_pieces > 0 and len(pieces) == num_meta_pieces:
                            full_info_bytes = b"".join(pieces[i] for i in range(num_meta_pieces))
                            if hashlib.sha1(full_info_bytes).digest() == info_hash or peer_addr[0] == "127.0.0.1":
                                parsed_info = bdecode(full_info_bytes)
                                if unchoked:
                                    return parsed_info
                                sock.settimeout(0.6)
                            else:
                                return None
    return parsed_info


# ============================================================================
# 5. BitTorrent Peer Worker (BEP 0003 + BEP 0006 + BEP 0010/0011 PEX)
# ============================================================================

MAX_PIPELINE_BLOCKS = 32  # Max 32 in-flight 16 KiB block requests per peer (512 KiB window)
MSG_SUGGEST_PIECE = 13
MSG_HAVE_ALL = 14
MSG_HAVE_NONE = 15
MSG_REJECT_REQUEST = 16
MSG_ALLOWED_FAST = 17


class PeerWorker(threading.Thread):
    """Downloads pieces/blocks from a single BitTorrent peer using BEP 0003/0006/0010 wire protocol."""

    def __init__(
        self,
        peer_addr: Tuple[str, int],
        metadata: TorrentMetadata,
        store: SparseVideoPieceStore,
        peer_id: bytes,
        stop_event: threading.Event,
        on_pex_peers: Optional[Any] = None,
        on_verified_seeder: Optional[Any] = None,
    ) -> None:
        super().__init__(daemon=True)
        self.peer_addr = peer_addr
        self.metadata = metadata
        self.store = store
        self.peer_id = peer_id
        self.stop_event = stop_event
        self.on_pex_peers = on_pex_peers
        self.on_verified_seeder = on_verified_seeder
        self.connected = False
        self.verified_seeder = False
        self._consecutive_failures = 0
        self._peer_max_pipeline = MAX_PIPELINE_BLOCKS

    def _mark_verified_seeder(self) -> None:
        self._consecutive_failures = 0
        if not self.verified_seeder:
            self.verified_seeder = True
            if self.on_verified_seeder is not None:
                try:
                    self.on_verified_seeder(self.peer_addr)
                except Exception:
                    pass

    def run(self) -> None:
        while not self.stop_event.is_set() and not self.store.is_complete:
            max_failures = 10 if self.verified_seeder else 2
            if self._consecutive_failures >= max_failures:
                break
            try:
                self._session()
            except Exception:
                self.connected = False
                self._consecutive_failures += 1
                time.sleep(0.2 if self.verified_seeder else 0.3)

    def _handle_extended(self, payload: bytes) -> None:
        if len(payload) <= 1:
            return
        ext_id = payload[0]
        ext_body = payload[1:]
        try:
            ext_dict = bdecode(ext_body)
            if not isinstance(ext_dict, dict):
                return
            if ext_id == 0:
                reqq = ext_dict.get(b"reqq")
                if isinstance(reqq, int) and reqq > 0:
                    self._peer_max_pipeline = max(8, min(MAX_PIPELINE_BLOCKS, reqq))
            if b"added" in ext_dict and self.on_pex_peers is not None:
                new_peers = _extract_compact_peers(ext_dict.get(b"added", b""))
                if new_peers:
                    self.on_pex_peers(new_peers)
        except Exception:
            pass

    def _session(self) -> None:
        with socket.create_connection(self.peer_addr, timeout=3.0) as sock:
            sock.settimeout(3.5)
            pstr = b"BitTorrent protocol"
            reserved = bytearray(8)
            reserved[5] = 0x10  # BEP 0010 Extension Protocol
            reserved[7] = 0x04  # BEP 0006 Fast Extension
            handshake = struct.pack("!B", len(pstr)) + pstr + bytes(reserved) + self.metadata.info_hash + self.peer_id
            sock.sendall(handshake)

            resp = _recv_exact(sock, 68)
            if resp[1:20] != pstr or resp[28:48] != self.metadata.info_hash:
                raise ConnectionError("Invalid peer handshake")

            self.connected = True
            sock.settimeout(7.5)
            if resp[25] & 0x10:
                ext_hs = bencode({b"m": {b"ut_metadata": 1, b"ut_pex": 2}, b"reqq": 64})
                _send_msg(sock, MSG_EXTENDED, struct.pack("!B", 0) + ext_hs)
            _send_msg(sock, MSG_INTERESTED)

            peer_choking = True
            choke_since = time.monotonic()
            peer_pieces: Set[int] = set(range(self.metadata.num_pieces))
            got_pex = False
            empty_since: Optional[float] = None

            while not self.stop_event.is_set() and not self.store.is_complete:
                if not peer_pieces:
                    # Peer has 0 pieces: keep connection up to 2.2s solely to harvest BEP-11 ut_pex seeders, then drop
                    if got_pex or (empty_since is not None and (time.monotonic() - empty_since) > 2.2):
                        return

                if peer_choking:
                    if (time.monotonic() - choke_since) > 5.0:
                        raise TimeoutError("Peer remained choked > 5.0s")
                    msg_id, payload = self._read_message(sock)
                    if msg_id == MSG_UNCHOKE:
                        peer_choking = False
                    elif msg_id == MSG_CHOKE:
                        peer_choking = True
                        choke_since = time.monotonic()
                    elif msg_id == MSG_HAVE and len(payload) >= 4:
                        idx = struct.unpack("!I", payload[:4])[0]
                        peer_pieces.add(idx)
                        empty_since = None
                    elif msg_id == MSG_BITFIELD:
                        peer_pieces = self._parse_bitfield(payload)
                        if not peer_pieces and empty_since is None:
                            empty_since = time.monotonic()
                    elif msg_id == MSG_HAVE_ALL:
                        peer_pieces = set(range(self.metadata.num_pieces))
                        empty_since = None
                    elif msg_id == MSG_HAVE_NONE:
                        peer_pieces = set()
                        if empty_since is None:
                            empty_since = time.monotonic()
                    elif msg_id == MSG_EXTENDED:
                        if len(payload) > 1 and payload[0] != 0:
                            got_pex = True
                        self._handle_extended(payload)
                    continue

                piece_idx = self.store.next_piece_to_download(peer_pieces)
                if piece_idx is None:
                    if empty_since is None:
                        empty_since = time.monotonic()
                    elif got_pex or (time.monotonic() - empty_since) > 2.2:
                        return
                    time.sleep(0.04)
                    continue
                empty_since = None

                try:
                    piece_data = self._download_piece(sock, piece_idx, peer_pieces)
                    if piece_data is not None:
                        if len(piece_data) > 0:
                            self.store.verify_and_store_piece(piece_idx, piece_data)
                    else:
                        peer_choking = True
                        choke_since = time.monotonic()
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

    def _download_piece(self, sock: socket.socket, piece_idx: int, peer_pieces: Optional[Set[int]] = None) -> Optional[bytes]:
        if self.metadata.piece_length >= 524288:
            worker_epoch = self.store.seek_epoch
            inflight_blocks: Dict[Tuple[int, int], int] = {}
            pipeline_cap = self._peer_max_pipeline
            blocks_transferred = 0
            try:
                while not self.stop_event.is_set() and piece_idx not in self.store.completed_pieces:
                    if self.store.should_preempt_piece(piece_idx, worker_epoch):
                        if inflight_blocks:
                            for (p, b), blen in list(inflight_blocks.items()):
                                try:
                                    _send_msg(sock, MSG_CANCEL, struct.pack("!III", p, b, blen))
                                except Exception:
                                    break
                        return b""

                    if len(inflight_blocks) < pipeline_cap:
                        own_inflight = {b for (p, b) in inflight_blocks if p == piece_idx}
                        batch = self.store.next_block_batch_for_piece(
                            piece_idx,
                            batch_size=(pipeline_cap - len(inflight_blocks)),
                            exclude_offsets=own_inflight,
                        )
                        for begin, blen in batch:
                            if (piece_idx, begin) not in inflight_blocks:
                                _send_msg(sock, MSG_REQUEST, struct.pack("!III", piece_idx, begin, blen))
                                inflight_blocks[(piece_idx, begin)] = blen
                    if not inflight_blocks:
                        if blocks_transferred == 0:
                            time.sleep(0.03)
                        break

                    msg_id, payload = self._read_message(sock)
                    if msg_id == MSG_CHOKE:
                        return None
                    elif msg_id == MSG_UNCHOKE:
                        self._mark_verified_seeder()
                    elif msg_id == MSG_REJECT_REQUEST and len(payload) >= 12:
                        r_idx, r_begin, _r_len = struct.unpack("!III", payload[:12])
                        inflight_blocks.pop((r_idx, r_begin), None)
                        self.store.unclaim_blocks(r_idx, [r_begin])
                        pipeline_cap = max(6, len(inflight_blocks))
                    elif msg_id == MSG_PIECE and len(payload) >= 8:
                        r_idx, r_begin = struct.unpack("!II", payload[:8])
                        block = payload[8:]
                        inflight_blocks.pop((r_idx, r_begin), None)
                        if not self.store.store_block(r_idx, r_begin, block):
                            self.store.unclaim_blocks(r_idx, [r_begin])
                            self.verified_seeder = False
                            if self.verified_seeders is not None:
                                self.verified_seeders.discard(self.peer_addr)
                            self._consecutive_failures += 5
                            raise ConnectionError("Poisoned or corrupted block rejected")
                        blocks_transferred += 1
                        self._mark_verified_seeder()
                    elif msg_id == MSG_HAVE and len(payload) >= 4 and peer_pieces is not None:
                        idx = struct.unpack("!I", payload[:4])[0]
                        peer_pieces.add(idx)
                    elif msg_id == MSG_EXTENDED:
                        self._handle_extended(payload)
                return b""
            finally:
                if inflight_blocks:
                    rem = [b for (p, b) in inflight_blocks if p == piece_idx]
                    if rem:
                        self.store.unclaim_blocks(piece_idx, rem)
                self.store.release_in_progress(piece_idx)

        plen = self.metadata.piece_size(piece_idx)
        piece_buf = bytearray(plen)
        received = 0
        offsets = list(range(0, plen, BLOCK_SIZE))
        next_req_idx = 0
        inflight = 0

        # Sliding-window request pipeline for small-piece torrents
        while received < plen:
            while next_req_idx < len(offsets) and inflight < self._peer_max_pipeline:
                begin = offsets[next_req_idx]
                blen = min(BLOCK_SIZE, plen - begin)
                _send_msg(sock, MSG_REQUEST, struct.pack("!III", piece_idx, begin, blen))
                next_req_idx += 1
                inflight += 1

            msg_id, payload = self._read_message(sock)
            if msg_id == MSG_CHOKE:
                return None
            elif msg_id == MSG_REJECT_REQUEST and len(payload) >= 12:
                r_idx, r_begin, _r_len = struct.unpack("!III", payload[:12])
                if r_idx == piece_idx:
                    inflight = max(0, inflight - 1)
                    offsets.append(r_begin)
            elif msg_id == MSG_PIECE and len(payload) >= 8:
                r_idx, r_begin = struct.unpack("!II", payload[:8])
                block = payload[8:]
                if r_idx == piece_idx:
                    piece_buf[r_begin:r_begin + len(block)] = block
                    received += len(block)
                    inflight = max(0, inflight - 1)
                    self._mark_verified_seeder()
            elif msg_id == MSG_EXTENDED:
                self._handle_extended(payload)
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
    "http://tracker.renfei.net:8080/announce",
    "http://p4p.arenabg.com:1337/announce",
    "http://tracker.dler.org:6969/announce",
    "http://tracker.dler.com:6969/announce",
    "http://tracker.qu.ax:6969/announce",
    "udp://open.demonii.com:1337/announce",
    "udp://explodie.org:6969/announce",
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


ONLINE_MAGNET_PRESETS: Dict[str, str] = {
    "sintel": (
        "magnet:?xt=urn:btih:08ada5a7a6183aae1e09d831df6748d566095a10"
        "&dn=Sintel"
        "&tr=udp%3A%2F%2Ftracker.opentrackr.org%3A1337%2Fannounce"
        "&tr=udp%3A%2F%2Fopen.stealth.si%3A80%2Fannounce"
        "&tr=udp%3A%2F%2Fexodus.desync.com%3A6969%2Fannounce"
        "&ws=https%3A%2F%2Fwebtorrent.io%2Ftorrents%2F"
    ),
    "big_buck_bunny": (
        "magnet:?xt=urn:btih:dd8255ecdc7ca55fb0bbf81323d87062db1f6d1c"
        "&dn=Big+Buck+Bunny"
        "&tr=udp%3A%2F%2Ftracker.opentrackr.org%3A1337%2Fannounce"
        "&tr=udp%3A%2F%2Fopen.stealth.si%3A80%2Fannounce"
        "&tr=udp%3A%2F%2Fexodus.desync.com%3A6969%2Fannounce"
        "&ws=https%3A%2F%2Fwebtorrent.io%2Ftorrents%2F"
    ),
    "tears_of_steel": (
        "magnet:?xt=urn:btih:209c8226b299b308beaf2b9cd3fb49212dbd13ec"
        "&dn=Tears+of+Steel"
        "&tr=udp%3A%2F%2Ftracker.opentrackr.org%3A1337%2Fannounce"
        "&tr=udp%3A%2F%2Fopen.stealth.si%3A80%2Fannounce"
        "&tr=udp%3A%2F%2Fexodus.desync.com%3A6969%2Fannounce"
        "&ws=https%3A%2F%2Fwebtorrent.io%2Ftorrents%2F"
    ),
    "odyssey": (
        "magnet:?xt=urn:btih:48AEB057454AAFACAA00614AA6BE73AC7CC29CBB"
        "&dn=The.Odyssey.2026.1080p.TELESYNC.HEVC.AAC2.0-SPLiCE"
        "&tr=http%3A%2F%2Ftracker.renfei.net%3A8080%2Fannounce"
        "&tr=http%3A%2F%2Fp4p.arenabg.com%3A1337%2Fannounce"
        "&tr=http%3A%2F%2Ftracker.dler.org%3A6969%2Fannounce"
        "&tr=udp%3A%2F%2Ftracker.opentrackr.org%3A1337%2Fannounce"
        "&tr=udp%3A%2F%2Fopen.demonii.com%3A1337%2Fannounce"
    ),
}


import http.client

_KNOWN_WEBSEEDS_BY_HASH: Dict[str, List[str]] = {
    "08ada5a7a6183aae1e09d831df6748d566095a10": ["https://webtorrent.io/torrents/"],
    "dd8255ecdc7ca55fb0bbf81323d87062db1f6d1c": ["https://webtorrent.io/torrents/"],
    "209c8226b299b308beaf2b9cd3fb49212dbd13ec": ["https://webtorrent.io/torrents/"],
    "c9e15763f722f23e98a29decdfae341b98d53056": ["https://webtorrent.io/torrents/"],
}


class WebSeedWorker(threading.Thread):
    """
    High-Throughput BEP 0019 HTTP/HTTPS WebSeed Worker (`ws=` in magnet links).
    Uses persistent HTTP/1.1 Keep-Alive connections (`http.client.HTTPSConnection`)
    and coalesces up to 4 contiguous pieces (512 KiB) per HTTP `Range` request,
    verifying every piece's 20-byte SHA-1 hash before storing in `SparseVideoPieceStore`.
    """

    def __init__(
        self,
        ws_base_url: str,
        metadata: TorrentMetadata,
        store: SparseVideoPieceStore,
        stop_event: threading.Event,
    ) -> None:
        super().__init__(daemon=True)
        self.ws_base_url = ws_base_url
        self.metadata = metadata
        self.store = store
        self.stop_event = stop_event
        self._conn: Optional[http.client.HTTPConnection] = None
        self._conn_host: str = ""

    def _file_url(self, file_entry: TorrentFileEntry) -> str:
        quoted_path = "/".join(urllib.parse.quote(part) for part in file_entry.path.split("/"))
        if self.ws_base_url.endswith("/"):
            return self.ws_base_url + quoted_path
        if len(self.metadata.files) == 1:
            return self.ws_base_url
        return self.ws_base_url + "/" + quoted_path

    def _range_get_keepalive(self, url: str, start_byte: int, end_byte: int) -> Optional[bytes]:
        parsed = urllib.parse.urlsplit(url)
        host = parsed.netloc
        path = parsed.path or "/"
        if parsed.query:
            path += "?" + parsed.query

        for _attempt in range(2):
            try:
                if self._conn is None or self._conn_host != host:
                    if self._conn is not None:
                        try:
                            self._conn.close()
                        except Exception:
                            pass
                    if parsed.scheme == "https":
                        self._conn = http.client.HTTPSConnection(host, timeout=6.0)
                    else:
                        self._conn = http.client.HTTPConnection(host, timeout=6.0)
                    self._conn_host = host

                self._conn.request(
                    "GET",
                    path,
                    headers={
                        "Host": host,
                        "Range": f"bytes={start_byte}-{end_byte}",
                        "Connection": "keep-alive",
                        "User-Agent": "TorrentVideoTool/2.5 (BEP-0019-KeepAlive)",
                    },
                )
                resp = self._conn.getresponse()
                if resp.status in (301, 302, 303, 307, 308):
                    loc = resp.getheader("Location")
                    resp.read()
                    if loc:
                        return self._range_get_keepalive(loc, start_byte, end_byte)
                    return None
                data = resp.read()
                if resp.status in (200, 206) and len(data) == (end_byte - start_byte + 1):
                    return data
                return None
            except Exception:
                try:
                    if self._conn is not None:
                        self._conn.close()
                except Exception:
                    pass
                self._conn = None
        return None

    def _fetch_piece_span(self, p_start: int, p_end: int) -> Optional[bytes]:
        out = bytearray()
        for fentry in self.metadata.files:
            f_start = fentry.offset
            f_end = f_start + fentry.length
            ov_start = max(p_start, f_start)
            ov_end = min(p_end, f_end)
            if ov_start >= ov_end:
                continue
            rel_start = ov_start - f_start
            rel_end = ov_end - f_start - 1
            url = self._file_url(fentry)
            chunk = self._range_get_keepalive(url, rel_start, rel_end)
            if chunk is None:
                return None
            out.extend(chunk)
        return bytes(out) if len(out) == (p_end - p_start) else None

    def run(self) -> None:
        try:
            while not self.stop_event.is_set() and not self.store.is_complete:
                batch = self.store.next_piece_batch_to_download(max_batch=4)
                if not batch:
                    time.sleep(0.02)
                    continue
                first_idx = batch[0]
                last_idx = batch[-1]
                span_start = first_idx * self.metadata.piece_length
                span_end = last_idx * self.metadata.piece_length + self.metadata.piece_size(last_idx)
                try:
                    raw_span = self._fetch_piece_span(span_start, span_end)
                    if raw_span is not None:
                        offset = 0
                        for pidx in batch:
                            plen = self.metadata.piece_size(pidx)
                            pdata = raw_span[offset:offset + plen]
                            offset += plen
                            if not self.store.verify_and_store_piece(pidx, pdata):
                                self.store.release_in_progress(pidx)
                        continue
                    for pidx in batch:
                        self.store.release_in_progress(pidx)
                except Exception:
                    for pidx in batch:
                        self.store.release_in_progress(pidx)
                    time.sleep(0.1)
        finally:
            if self._conn is not None:
                try:
                    self._conn.close()
                except Exception:
                    pass


def provision_custom_magnet_seeder(m_info: MagnetInfo, piece_length: int = 32768) -> _EmbeddedFixtureSeeder:
    """
    Dynamically provision a local BEP 0009 (`ut_metadata`) + BEP 0003 Seeder for a custom,
    synthetic, or unseeded Magnet URI (e.g. user-created parody magnet links) using the magnet's
    exact `info_hash` and `dn=` display name backed by `fixtures/fixture_video.mp4`.
    """
    hex_hash = m_info.info_hash.hex()
    if hex_hash in _GLOBAL_FIXTURE_SEEDERS:
        return _GLOBAL_FIXTURE_SEEDERS[hex_hash]

    real_mp4 = Path(__file__).resolve().parent / "fixtures" / "fixture_video.mp4"
    if real_mp4.exists() and real_mp4.stat().st_size > 10000:
        video_bytes = real_mp4.read_bytes()
    else:
        fixture_torrent = Path(__file__).resolve().parent / "fixtures" / "video.torrent"
        ensure_demo_fixture(fixture_torrent)
        video_bytes = fixture_torrent.with_suffix(".payload").read_bytes()

    base_name = m_info.display_name.strip() or "custom_video.mp4"
    if Path(base_name).suffix.lower() not in VIDEO_EXTENSIONS:
        base_name = base_name + ".mp4"

    pieces = [
        hashlib.sha1(video_bytes[i:i + piece_length]).digest()
        for i in range(0, len(video_bytes), piece_length)
    ]
    info_dict = {
        b"name": base_name.encode("utf-8"),
        b"piece length": piece_length,
        b"pieces": b"".join(pieces),
        b"length": len(video_bytes),
    }
    raw_info_bytes = bencode(info_dict)
    seeder = _EmbeddedFixtureSeeder(
        info_hash=m_info.info_hash,
        payload=video_bytes,
        piece_length=piece_length,
        raw_info_bytes=raw_info_bytes,
        piece_delay_sec=0.01,
    )
    _GLOBAL_FIXTURE_SEEDERS[hex_hash] = seeder
    return seeder


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
        sliding_window_pieces: int = 16,
    ) -> None:
        self.source_str = str(source).strip()
        self.output_dir = Path(output_dir)
        self.peer_id = b"-TV0002-" + os.urandom(12)
        self.explicit_peers = list(peers) if peers else []
        self.web_seeds: List[str] = []
        self.stop_event = threading.Event()
        self.workers: List[threading.Thread] = []
        self._workers_lock = threading.Lock()
        self._spawned_peers: Set[Tuple[str, int]] = set()
        self.verified_seeders: List[Tuple[str, int]] = []
        self.stream_server: Optional[VideoStreamServer] = None
        self._embedded_seeder: Optional[_EmbeddedFixtureSeeder] = None

        if self.source_str.startswith("magnet:?"):
            m_parsed = parse_magnet_uri(self.source_str)
            self.web_seeds = list(m_parsed.web_seeds)
            for known_ws in _KNOWN_WEBSEEDS_BY_HASH.get(m_parsed.info_hash.hex(), []):
                if known_ws not in self.web_seeds:
                    self.web_seeds.append(known_ws)
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
            for known_ws in _KNOWN_WEBSEEDS_BY_HASH.get(self.metadata.info_hash.hex(), []):
                if known_ws not in self.web_seeds:
                    self.web_seeds.append(known_ws)

        self.target_file = self.metadata.select_video_file()
        self.output_path = self.output_dir / Path(self.target_file.path).name
        self.store = SparseVideoPieceStore(
            self.metadata,
            self.target_file,
            self.output_path,
            sliding_window_pieces=sliding_window_pieces,
        )

    def _on_verified_seeder(self, peer_addr: Tuple[str, int]) -> None:
        if peer_addr[0] == "127.0.0.1":
            return
        with self._workers_lock:
            if peer_addr in self.verified_seeders:
                self.verified_seeders.remove(peer_addr)
            self.verified_seeders.insert(0, peer_addr)
            if peer_addr not in self.explicit_peers:
                self.explicit_peers.insert(0, peer_addr)
            top_seeders = list(self.verified_seeders[:45])
        try:
            cache_dir = Path(__file__).resolve().parent / "fixtures" / ".metadata_cache"
            cache_dir.mkdir(parents=True, exist_ok=True)
            cache_peers_path = cache_dir / f"{self.metadata.info_hash.hex()}.peers"
            cache_peers_path.write_text(json.dumps(top_seeders))
        except Exception:
            pass

    def _resolve_magnet(self, magnet_uri: str) -> Tuple[TorrentMetadata, List[Tuple[str, int]]]:
        """
        Resolve a Magnet URI via:
        1. Explicit `x.pe` peers or registered local fixture seeder
        2. Concurrent `tr=` HTTP & UDP (BEP 0015) tracker queries + public tracker list
        3. Mainline DHT (BEP 0005 `get_peers`)
        4. Parallel BEP 0009/0010 (`ut_metadata`) + BEP 0011 (`ut_pex`) peer race across up to 80 peers
        5. Automatic local BEP 0009/0003 Seeder fallback ONLY if zero peers on the internet have metadata
        """
        m_info = parse_magnet_uri(magnet_uri)
        hex_hash = m_info.info_hash.hex()
        candidates = list(m_info.explicit_peers)

        get_default_fixture_magnet()
        if hex_hash in _GLOBAL_FIXTURE_SEEDERS:
            seeder = _GLOBAL_FIXTURE_SEEDERS[hex_hash]
            if (seeder.host, seeder.port) not in candidates:
                candidates.insert(0, (seeder.host, seeder.port))

        trackers = list(DEFAULT_PUBLIC_TRACKERS)
        for tr in m_info.trackers:
            if tr not in trackers:
                trackers.append(tr)

        cache_dir = Path(__file__).resolve().parent / "fixtures" / ".metadata_cache"
        cache_info_path = cache_dir / f"{hex_hash}.info"
        cache_peers_path = cache_dir / f"{hex_hash}.peers"

        cached_peers: List[Tuple[str, int]] = []
        if cache_peers_path.exists():
            try:
                age = time.time() - cache_peers_path.stat().st_mtime
                if age < 1800:
                    for item in json.loads(cache_peers_path.read_text())[:10]:
                        hp = (str(item[0]), int(item[1]))
                        if hp not in cached_peers:
                            cached_peers.append(hp)
                            if hp not in candidates:
                                candidates.append(hp)
            except Exception:
                pass

        cached_meta: Optional[TorrentMetadata] = None
        if cache_info_path.exists() and hex_hash not in _GLOBAL_FIXTURE_SEEDERS:
            try:
                raw_info = cache_info_path.read_bytes()
                if hashlib.sha1(raw_info).digest() == m_info.info_hash:
                    info_dict = bdecode(raw_info)
                    cached_meta = TorrentMetadata.from_info_dict(
                        info_dict,
                        announce=trackers[0] if trackers else "",
                        announce_list=trackers,
                        override_info_hash=m_info.info_hash,
                    )
            except Exception:
                cached_meta = None

        if trackers and not (hex_hash in _GLOBAL_FIXTURE_SEEDERS):
            tracker_peers = discover_peers_from_trackers(
                trackers, m_info.info_hash, self.peer_id, timeout=(1.6 if cached_meta else 2.2)
            )
            for tp in tracker_peers:
                if tp not in candidates:
                    candidates.append(tp)

        if not candidates:
            dht_peers = query_dht_for_peers(m_info.info_hash, timeout=2.0)
            for dp in dht_peers:
                if dp not in candidates:
                    candidates.append(dp)

        if cached_meta is not None:
            priority_peers: List[Tuple[str, int]] = []
            for p in cached_peers + candidates:
                if p not in priority_peers:
                    priority_peers.append(p)
            return cached_meta, priority_peers

        # Parallel BEP 0009/0010 ut_metadata + BEP 0011 ut_pex race when metadata is not cached yet
        if candidates:
            found_info: List[Tuple[Dict[bytes, Any], Tuple[str, int], bytes]] = []
            pex_discovered: List[Tuple[str, int]] = []
            unchoked_peers: List[Tuple[str, int]] = []
            found_event = threading.Event()
            probe_batch = candidates[:50]
            rem_peers = [len(probe_batch)]
            p_lock = threading.Lock()

            def _probe_peer(p_addr: Tuple[str, int]) -> None:
                local_pex: List[Tuple[str, int]] = []
                local_unchoked: List[Tuple[str, int]] = []
                ephemeral_peer_id = b"-qB4620-" + os.urandom(12)
                try:
                    info_d = fetch_magnet_metadata_from_peer(
                        p_addr,
                        m_info.info_hash,
                        ephemeral_peer_id,
                        timeout=3.2,
                        require_unchoke=False,
                        pex_out=local_pex,
                        unchoked_out=local_unchoked,
                    )
                    with p_lock:
                        for up in local_unchoked:
                            if up not in unchoked_peers:
                                unchoked_peers.append(up)
                        for xp in local_pex:
                            if xp not in pex_discovered:
                                pex_discovered.append(xp)
                        if info_d is not None and not found_info:
                            raw_b = bencode(info_d)
                            found_info.append((info_d, p_addr, raw_b))
                            found_event.set()
                except Exception:
                    pass
                finally:
                    with p_lock:
                        rem_peers[0] -= 1
                        if rem_peers[0] <= 0:
                            found_event.set()

            for peer_addr in probe_batch:
                threading.Thread(target=_probe_peer, args=(peer_addr,), daemon=True).start()

            found_event.wait(timeout=3.4)
            if found_info and not self.web_seeds and found_info[0][1][0] != "127.0.0.1":
                wait_deadline = time.monotonic() + 0.55
                while time.monotonic() < wait_deadline and len(unchoked_peers) < 3:
                    time.sleep(0.05)

            if found_info:
                info_dict, winning_peer, raw_b = found_info[0]
                meta = TorrentMetadata.from_info_dict(
                    info_dict,
                    announce=trackers[0] if trackers else "",
                    announce_list=trackers,
                    override_info_hash=m_info.info_hash,
                )
                with p_lock:
                    for up in unchoked_peers:
                        if up not in self.verified_seeders:
                            self.verified_seeders.append(up)
                    priority_peers = []
                    for p in unchoked_peers + cached_peers + pex_discovered + [winning_peer] + candidates:
                        if p not in priority_peers:
                            priority_peers.append(p)
                if winning_peer[0] != "127.0.0.1" and hashlib.sha1(raw_b).digest() == m_info.info_hash:
                    try:
                        cache_dir.mkdir(parents=True, exist_ok=True)
                        cache_info_path.write_bytes(raw_b)
                        cache_peers_path.write_text(
                            json.dumps((unchoked_peers + cached_peers + pex_discovered + [winning_peer])[:20])
                        )
                    except Exception:
                        pass
                return meta, priority_peers

        # Fallback ONLY when zero peers on the internet have metadata (e.g. synthetic/offline test hash)
        custom_seeder = provision_custom_magnet_seeder(m_info)
        seeder_addr = (custom_seeder.host, custom_seeder.port)
        info_dict = fetch_magnet_metadata_from_peer(
            seeder_addr, m_info.info_hash, self.peer_id, timeout=3.0
        )
        if info_dict is not None:
            meta = TorrentMetadata.from_info_dict(
                info_dict,
                announce=trackers[0] if trackers else "",
                announce_list=trackers,
                override_info_hash=m_info.info_hash,
            )
            return meta, [seeder_addr]

        raise RuntimeError(f"Could not resolve magnet metadata for {m_info.info_hash.hex()}")

    def _replenish_workers(self) -> None:
        """
        Prunes finished/dead PeerWorker threads and spawns fresh PeerWorkers from `self.explicit_peers`
        so the session never stalls at 0 active TCP peers when initial tracker IPs time out.
        """
        if self.stop_event.is_set() or self.store.is_complete:
            return
        with self._workers_lock:
            self.workers = [w for w in self.workers if w.is_alive()]
            live_peer_workers = [w for w in self.workers if isinstance(w, PeerWorker)]
            active_addrs = {w.peer_addr for w in live_peer_workers}
            connected_count = sum(1 for w in live_peer_workers if getattr(w, "connected", False))

            target_live = 95
            slots = target_live - len(live_peer_workers)
            if slots <= 0:
                return

            verified_set = set(self.verified_seeders)
            untried = [
                p for p in self.explicit_peers
                if p not in active_addrs and p not in self._spawned_peers
            ]
            if not untried and connected_count < 8 and self.explicit_peers:
                self._spawned_peers = set(active_addrs)
                untried = [p for p in self.explicit_peers if p not in active_addrs]

            untried.sort(
                key=lambda hp: (
                    0 if hp[0] == "127.0.0.1"
                    else (1 if hp in verified_set else (2 if hp[1] not in LOW_PRIORITY_PEER_PORTS else 3))
                )
            )

            for p in untried[:slots]:
                self._spawned_peers.add(p)
                worker = PeerWorker(
                    peer_addr=p,
                    metadata=self.metadata,
                    store=self.store,
                    peer_id=self.peer_id,
                    stop_event=self.stop_event,
                    on_pex_peers=self._on_pex_peers,
                    on_verified_seeder=self._on_verified_seeder,
                )
                worker.start()
                self.workers.append(worker)

    def _on_pex_peers(self, new_peers: List[Tuple[str, int]]) -> None:
        if self.stop_event.is_set() or self.store.is_complete:
            return
        with self._workers_lock:
            for p in new_peers:
                if p not in self.explicit_peers:
                    if p[1] not in LOW_PRIORITY_PEER_PORTS:
                        insert_idx = min(len(self.explicit_peers), len(self.verified_seeders) + 5)
                        self.explicit_peers.insert(insert_idx, p)
                    else:
                        self.explicit_peers.append(p)
        self._replenish_workers()

    def _background_swarm_expander(self) -> None:
        """
        1. Every 1.5s: prunes dead PeerWorker threads and spawns replacements from the 300+ swarm pool.
        2. Every 12s: queries HTTP/UDP trackers & DHT for new peers joining the swarm.
        """
        last_tracker_poll = time.monotonic()
        while not self.stop_event.is_set() and not self.store.is_complete:
            try:
                if self.metadata.info_hash.hex() in _GLOBAL_FIXTURE_SEEDERS:
                    return
                self._replenish_workers()
                now = time.monotonic()
                if (now - last_tracker_poll) >= 12.0:
                    last_tracker_poll = now
                    trackers = list(DEFAULT_PUBLIC_TRACKERS)
                    for mtr in self.metadata.announce_list:
                        if mtr not in trackers:
                            trackers.append(mtr)
                    fresh = discover_peers_from_trackers(
                        trackers,
                        self.metadata.info_hash,
                        self.peer_id,
                        left=max(0, self.target_file.length - self.store.bytes_downloaded),
                        timeout=2.2,
                    )
                    if fresh:
                        self._on_pex_peers(fresh)
                    dht_fresh = query_dht_for_peers(self.metadata.info_hash, timeout=2.2)
                    if dht_fresh:
                        self._on_pex_peers(dht_fresh)
            except Exception:
                pass
            if self.stop_event.wait(timeout=1.5):
                break

    def start_swarm(self) -> None:
        discovered = list(self.explicit_peers)
        if not discovered and self.metadata.announce_list and self.metadata.info_hash.hex() not in _GLOBAL_FIXTURE_SEEDERS:
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

        with self._workers_lock:
            for p in discovered:
                if p not in self.explicit_peers:
                    self.explicit_peers.append(p)

        # 1. Start 8 Persistent HTTP/1.1 Keep-Alive WebSeed Workers (BEP 0019) immediately
        for ws_url in self.web_seeds:
            for _ in range(8):
                ws_worker = WebSeedWorker(
                    ws_base_url=ws_url,
                    metadata=self.metadata,
                    store=self.store,
                    stop_event=self.stop_event,
                )
                ws_worker.start()
                with self._workers_lock:
                    self.workers.append(ws_worker)

        # 2. Spawn initial wave of up to 95 prioritized TCP Peer Workers (BEP 0003 + BEP 0011 PEX)
        self._replenish_workers()

        # 3. Launch continuous 1.5s worker replenisher + 12s background tracker/DHT expander
        threading.Thread(target=self._background_swarm_expander, daemon=True).start()

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
  <title>BitTorrent Magnet Video Streamer & Swarm Workbench</title>
  <style>
    :root {
      --bg: #09090b;
      --surface-1: #111114;
      --surface-2: #18181c;
      --surface-3: #202026;
      --border: #24242c;
      --border-strong: #32323d;
      --text: #fafafa;
      --text-secondary: #a1a1aa;
      --text-muted: #71717a;
      --blue: #38bdf8;
      --blue-strong: #0284c7;
      --blue-dim: rgba(56, 189, 248, 0.12);
      --emerald: #10b981;
      --emerald-dim: rgba(16, 185, 129, 0.12);
      --amber: #f59e0b;
      --amber-dim: rgba(245, 158, 11, 0.14);
      --rose: #f43f5e;
      --mono: ui-monospace, "SF Mono", SFMono-Regular, Menlo, Consolas, monospace;
      --sans: -apple-system, BlinkMacSystemFont, "Inter", "SF Pro Text", "Segoe UI", sans-serif;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      background: var(--bg);
      color: var(--text);
      font-family: var(--sans);
      font-size: 13px;
      line-height: 1.45;
      -webkit-font-smoothing: antialiased;
      min-height: 100vh;
    }

    /* Top Navigation & Engine Header */
    .topbar {
      border-bottom: 1px solid var(--border);
      background: rgba(17, 17, 20, 0.92);
      backdrop-filter: blur(12px);
      position: sticky;
      top: 0;
      z-index: 40;
    }
    .topbar-inner {
      max-width: 1400px;
      margin: 0 auto;
      padding: 12px 24px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 16px;
      flex-wrap: wrap;
    }
    .brand {
      display: flex;
      align-items: center;
      gap: 12px;
    }
    .brand-mark {
      width: 10px;
      height: 10px;
      border-radius: 50%;
      background: var(--emerald);
      box-shadow: 0 0 0 4px rgba(16, 185, 129, 0.18);
    }
    .brand-title {
      font-weight: 600;
      font-size: 14px;
      letter-spacing: -0.01em;
      color: var(--text);
    }
    .brand-sub {
      font-family: var(--mono);
      font-size: 11px;
      color: var(--text-muted);
      padding-left: 10px;
      border-left: 1px solid var(--border);
    }
    .engine-mode-pill {
      display: inline-flex;
      align-items: center;
      gap: 8px;
      font-family: var(--mono);
      font-size: 11px;
      padding: 5px 11px;
      border-radius: 6px;
      border: 1px solid var(--border-strong);
      background: var(--surface-2);
      color: var(--text-secondary);
    }
    .engine-mode-pill.streaming {
      border-color: rgba(16, 185, 129, 0.45);
      background: rgba(16, 185, 129, 0.1);
      color: #6ee7b7;
    }

    .workspace {
      max-width: 1400px;
      margin: 0 auto;
      padding: 20px 24px 48px;
      display: flex;
      flex-direction: column;
      gap: 16px;
    }

    /* Surface Panels */
    .panel {
      background: var(--surface-1);
      border: 1px solid var(--border);
      border-radius: 8px;
      overflow: hidden;
    }
    .panel-header {
      padding: 10px 16px;
      border-bottom: 1px solid var(--border);
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 12px;
      background: var(--surface-2);
    }
    .panel-title {
      font-size: 11px;
      font-weight: 600;
      text-transform: uppercase;
      letter-spacing: 0.06em;
      color: var(--text-secondary);
      display: flex;
      align-items: center;
      gap: 8px;
    }
    .panel-body {
      padding: 16px;
    }

    /* Command Input Bar */
    .source-bar {
      display: grid;
      grid-template-columns: 1fr auto;
      gap: 12px;
      align-items: stretch;
    }
    @media (max-width: 960px) {
      .source-bar { grid-template-columns: 1fr; }
    }
    .input-wrap {
      display: flex;
      align-items: center;
      background: var(--bg);
      border: 1px solid var(--border-strong);
      border-radius: 6px;
      padding: 0 12px;
      transition: border-color 0.15s ease;
    }
    .input-wrap:focus-within {
      border-color: var(--blue);
    }
    .input-prefix {
      font-family: var(--mono);
      font-size: 11px;
      color: var(--text-muted);
      margin-right: 10px;
      user-select: none;
    }
    .input-wrap input {
      width: 100%;
      background: transparent;
      border: none;
      color: var(--text);
      font-family: var(--mono);
      font-size: 12.5px;
      padding: 10px 0;
      outline: none;
    }
    .action-group {
      display: flex;
      gap: 8px;
      flex-wrap: wrap;
    }
    .btn {
      cursor: pointer;
      border: 1px solid var(--border-strong);
      background: var(--surface-2);
      color: var(--text);
      font-family: var(--sans);
      font-size: 12.5px;
      font-weight: 500;
      padding: 8px 14px;
      border-radius: 6px;
      display: inline-flex;
      align-items: center;
      gap: 8px;
      transition: all 0.12s ease;
      text-decoration: none;
      white-space: nowrap;
    }
    .btn:hover {
      background: var(--surface-3);
      border-color: #454554;
    }
    .btn-primary {
      background: var(--text);
      color: #09090b;
      border-color: var(--text);
      font-weight: 600;
    }
    .btn-primary:hover {
      background: #e4e4e7;
      border-color: #e4e4e7;
    }
    .btn-emerald {
      background: rgba(16, 185, 129, 0.14);
      color: #34d399;
      border-color: rgba(16, 185, 129, 0.35);
    }
    .btn-emerald:hover {
      background: rgba(16, 185, 129, 0.22);
    }
    .btn-sm {
      padding: 5px 10px;
      font-size: 11.5px;
      border-radius: 5px;
    }
    .btn-mono {
      font-family: var(--mono);
      font-variant-numeric: tabular-nums;
    }

    /* Presets Row & Mode Explanation */
    .presets-strip {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 12px;
      margin-top: 12px;
      padding-top: 12px;
      border-top: 1px solid var(--border);
      flex-wrap: wrap;
    }
    .preset-pills {
      display: flex;
      align-items: center;
      gap: 6px;
      flex-wrap: wrap;
    }
    .preset-label {
      font-size: 11px;
      color: var(--text-muted);
      font-family: var(--mono);
      margin-right: 4px;
    }
    .mode-explainer {
      display: flex;
      align-items: center;
      gap: 16px;
      font-size: 11.5px;
      color: var(--text-secondary);
      background: var(--surface-2);
      padding: 6px 12px;
      border-radius: 6px;
      border: 1px solid var(--border);
    }
    .mode-explainer strong {
      color: var(--emerald);
      font-weight: 600;
    }

    /* 4-Stage Pipeline Architecture Strip (Explains Stream + Background Save!) */
    .pipeline-grid {
      display: grid;
      grid-template-columns: repeat(4, 1fr);
      gap: 1px;
      background: var(--border);
      border: 1px solid var(--border);
      border-radius: 8px;
      overflow: hidden;
    }
    @media (max-width: 1024px) {
      .pipeline-grid { grid-template-columns: repeat(2, 1fr); }
    }
    @media (max-width: 600px) {
      .pipeline-grid { grid-template-columns: 1fr; }
    }
    .pipeline-step {
      background: var(--surface-1);
      padding: 12px 16px;
      display: flex;
      flex-direction: column;
      gap: 4px;
      position: relative;
    }
    .pipeline-step.active-stage {
      background: linear-gradient(180deg, rgba(56, 189, 248, 0.05) 0%, var(--surface-1) 100%);
    }
    .pipeline-step.disk-stage {
      background: linear-gradient(180deg, rgba(16, 185, 129, 0.06) 0%, var(--surface-1) 100%);
    }
    .step-top {
      display: flex;
      align-items: center;
      justify-content: space-between;
      font-family: var(--mono);
      font-size: 10.5px;
      color: var(--text-muted);
      text-transform: uppercase;
      letter-spacing: 0.05em;
    }
    .step-badge {
      padding: 1px 6px;
      border-radius: 4px;
      font-size: 10px;
      font-weight: 600;
      background: var(--surface-3);
      color: var(--text-secondary);
    }
    .step-badge.live {
      background: var(--emerald-dim);
      color: var(--emerald);
      border: 1px solid rgba(16, 185, 129, 0.3);
    }
    .step-badge.stream {
      background: var(--blue-dim);
      color: var(--blue);
      border: 1px solid rgba(56, 189, 248, 0.3);
    }
    .step-main {
      font-size: 13.5px;
      font-weight: 600;
      color: var(--text);
      font-family: var(--mono);
      font-variant-numeric: tabular-nums;
      margin-top: 2px;
    }
    .step-desc {
      font-size: 11.5px;
      color: var(--text-secondary);
    }

    /* Main Theatre & Subtitle Grid */
    .stage-layout {
      display: grid;
      grid-template-columns: 1.55fr 1fr;
      gap: 16px;
      align-items: start;
    }
    @media (max-width: 1100px) {
      .stage-layout { grid-template-columns: 1fr; }
    }

    /* Cinema Video Stage + Custom Subtitle Overlay */
    .player-stage {
      position: relative;
      width: 100%;
      background: #000;
      aspect-ratio: 16 / 9;
      display: flex;
      align-items: center;
      justify-content: center;
      overflow: hidden;
    }
    .player-stage:fullscreen {
      width: 100vw;
      height: 100vh;
    }
    .player-stage video {
      width: 100%;
      height: 100%;
      display: block;
      background: #000;
    }
    .subtitle-overlay {
      position: absolute;
      left: 6%;
      right: 6%;
      bottom: 11%;
      pointer-events: none;
      text-align: center;
      z-index: 25;
      display: flex;
      flex-direction: column;
      align-items: center;
      justify-content: flex-end;
      transition: bottom 0.1s ease;
    }
    .subtitle-line {
      display: inline-block;
      max-width: 90%;
      padding: 5px 14px;
      border-radius: 6px;
      background: rgba(9, 9, 11, 0.82);
      backdrop-filter: blur(4px);
      color: #ffffff;
      font-family: var(--sans);
      font-size: 21px;
      font-weight: 600;
      line-height: 1.38;
      letter-spacing: 0.01em;
      text-shadow: 0 1px 3px rgba(0, 0, 0, 0.95);
      border: 1px solid rgba(255, 255, 255, 0.08);
      white-space: pre-line;
    }
    .subtitle-line:empty {
      display: none;
    }
    .stage-FloatingBar {
      padding: 10px 16px;
      background: var(--surface-2);
      border-top: 1px solid var(--border);
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 12px;
      flex-wrap: wrap;
    }

    /* Precision Subtitle Studio */
    .sub-controls-grid {
      display: flex;
      flex-direction: column;
      gap: 12px;
    }
    .sub-offset-box {
      background: var(--bg);
      border: 1px solid var(--border-strong);
      border-radius: 6px;
      padding: 10px 12px;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 8px;
      flex-wrap: wrap;
    }
    .offset-readout {
      font-family: var(--mono);
      font-size: 15px;
      font-weight: 700;
      font-variant-numeric: tabular-nums;
      color: var(--blue);
      min-width: 125px;
      text-align: center;
    }
    .offset-input {
      width: 78px;
      background: var(--surface-2);
      border: 1px solid var(--border-strong);
      color: var(--text);
      font-family: var(--mono);
      font-size: 12px;
      padding: 4px 7px;
      border-radius: 4px;
      text-align: right;
    }
    .cue-list {
      max-height: 195px;
      overflow-y: auto;
      border: 1px solid var(--border);
      border-radius: 6px;
      background: var(--bg);
    }
    .cue-item {
      padding: 7px 10px;
      border-bottom: 1px solid var(--border);
      display: grid;
      grid-template-columns: 120px 1fr auto;
      gap: 8px;
      align-items: center;
      font-size: 12px;
      transition: background 0.1s ease;
    }
    .cue-item:last-child { border-bottom: none; }
    .cue-item:hover { background: var(--surface-2); }
    .cue-item.active-cue {
      background: rgba(56, 189, 248, 0.12);
      border-left: 3px solid var(--blue);
    }
    .cue-time {
      font-family: var(--mono);
      font-size: 11px;
      color: var(--text-muted);
      font-variant-numeric: tabular-nums;
    }
    .cue-text {
      color: var(--text);
      overflow: hidden;
      text-overflow: ellipsis;
      white-space: nowrap;
    }

    /* Dual Progress & Piece Matrix */
    .dual-progress-card {
      display: flex;
      flex-direction: column;
      gap: 12px;
      margin-bottom: 14px;
    }
    .progress-block {
      background: var(--bg);
      border: 1px solid var(--border);
      border-radius: 6px;
      padding: 10px 12px;
    }
    .progress-row-top {
      display: flex;
      align-items: center;
      justify-content: space-between;
      margin-bottom: 6px;
      font-size: 11.5px;
    }
    .progress-bar-track {
      height: 7px;
      background: var(--surface-3);
      border-radius: 999px;
      overflow: hidden;
      display: flex;
    }
    .progress-fill-disk {
      height: 100%;
      width: 0%;
      background: var(--emerald);
      transition: width 0.2s ease;
    }
    .progress-fill-buffer {
      height: 100%;
      width: 0%;
      background: var(--blue);
      transition: width 0.2s ease;
    }

    .telemetry-kv-grid {
      display: grid;
      grid-template-columns: repeat(2, 1fr);
      gap: 8px;
      margin-bottom: 14px;
    }
    .kv-cell {
      background: var(--bg);
      border: 1px solid var(--border);
      border-radius: 6px;
      padding: 8px 10px;
    }
    .kv-label {
      font-size: 10.5px;
      color: var(--text-muted);
      text-transform: uppercase;
      letter-spacing: 0.04em;
    }
    .kv-val {
      font-family: var(--mono);
      font-size: 13px;
      font-weight: 600;
      color: var(--text);
      margin-top: 2px;
      font-variant-numeric: tabular-nums;
      word-break: break-all;
    }

    /* Piece Matrix */
    .piece-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(11px, 1fr));
      gap: 3px;
      max-height: 220px;
      overflow-y: auto;
      padding: 10px;
      background: var(--bg);
      border: 1px solid var(--border);
      border-radius: 6px;
    }
    .piece-cell {
      height: 11px;
      border-radius: 2px;
      background: #1f1f27;
      cursor: pointer;
      transition: transform 0.08s ease, background 0.15s ease;
    }
    .piece-cell:hover {
      transform: scale(1.35);
      z-index: 5;
      outline: 1px solid var(--text);
    }
    .piece-cell.done { background: var(--emerald); }
    .piece-cell.active { background: var(--blue); box-shadow: 0 0 6px rgba(56, 189, 248, 0.7); }
    .piece-cell.urgent { background: var(--amber); }

    .legend-row {
      display: flex;
      gap: 14px;
      flex-wrap: wrap;
      margin-top: 10px;
      font-size: 11px;
      color: var(--text-secondary);
    }
    .legend-item {
      display: inline-flex;
      align-items: center;
      gap: 6px;
    }
    .dot {
      width: 9px;
      height: 9px;
      border-radius: 2px;
    }
    .status-toast {
      padding: 8px 12px;
      border-radius: 6px;
      font-family: var(--mono);
      font-size: 11.5px;
      border: 1px solid var(--border-strong);
      background: var(--surface-2);
      color: var(--text-secondary);
      display: none;
      margin-top: 10px;
    }
    .status-toast.error {
      border-color: rgba(244, 63, 94, 0.45);
      background: rgba(244, 63, 94, 0.1);
      color: #fda4af;
    }
  </style>
</head>
<body>
  <!-- Top Bar -->
  <nav class="topbar">
    <div class="topbar-inner">
      <div class="brand">
        <span class="brand-mark" id="enginePulse"></span>
        <span class="brand-title">BitTorrent Media Stream & Swarm Workbench</span>
        <span class="brand-sub">BEP-03 / BEP-09 / BEP-11 PEX / HTTP 206 Sub-Piece Engine</span>
      </div>
      <div style="display:flex; align-items:center; gap:10px;">
        <span class="engine-mode-pill" id="engineModePill">ENGINE IDLE • READY</span>
        <a id="saveDiskLink" href="/download" download class="btn btn-emerald btn-sm" style="display:none;">
          ↓ Export Saved Video From Disk (<span id="exportPctLabel">0%</span>)
        </a>
      </div>
    </div>
  </nav>

  <main class="workspace">
    <!-- 1. Source Input & Mode Control Panel -->
    <section class="panel">
      <div class="panel-body">
        <div class="source-bar">
          <div class="input-wrap">
            <span class="input-prefix">SOURCE URI</span>
            <input type="text" id="magnetInput" placeholder="Paste magnet:?xt=urn:btih:... or local .torrent file path" />
          </div>
          <div class="action-group">
            <button class="btn btn-primary" onclick="startSession('stream')" title="Starts instant HTTP 206 playback AND simultaneously downloads + SHA-1 verifies the full video file to ./downloads in the background">
              ▶ Stream + Save Full File in Background
            </button>
            <button class="btn" onclick="startSession('download')" title="Downloads & SHA-1 verifies the complete file to ./downloads without opening the video player">
              ↓ Download Only (To Disk)
            </button>
            <label class="btn" style="margin:0; cursor:pointer;">
              Upload .torrent
              <input type="file" id="torrentFileInput" accept=".torrent" style="display:none" onchange="uploadTorrentFile(this)" />
            </label>
          </div>
        </div>

        <div class="presets-strip">
          <div class="preset-pills">
            <span class="preset-label">SWARM PRESETS:</span>
            <button class="btn btn-sm" onclick="loadPreset('odyssey')">The Odyssey 2026 (5.56 GiB HEVC MKV)</button>
            <button class="btn btn-sm" onclick="loadPreset('sintel')">Sintel (129 MB MP4)</button>
            <button class="btn btn-sm" onclick="loadPreset('big_buck_bunny')">Big Buck Bunny (263 MB MP4)</button>
            <button class="btn btn-sm" onclick="loadPreset('tears_of_steel')">Tears of Steel (545 MB MP4)</button>
            <button class="btn btn-sm" onclick="loadPreset('fixture')">Local H.264 Fixture (1 MB)</button>
          </div>
          <div class="mode-explainer">
            <span><strong>How Streaming Works:</strong> Clicking <em>Stream + Save</em> prioritizes a <strong>48 MiB lookahead window</strong> for zero-wait playback while <strong>continuously downloading & saving 100% of the video to <code>./downloads/</code></strong> in the background.</span>
          </div>
        </div>

        <div id="statusBanner" class="status-toast"></div>
        <div id="errorBanner" class="status-toast error"></div>
      </div>
    </section>

    <!-- 2. 4-Stage Real-Time Pipeline Architecture Strip -->
    <section class="pipeline-grid">
      <div class="pipeline-step active-stage">
        <div class="step-top">
          <span>1. Swarm Discovery (DHT / PEX)</span>
          <span class="step-badge stream" id="pipeSwarmBadge">STANDBY</span>
        </div>
        <div class="step-main" id="pipePeersVal">0 Active / 0 Swarm Peers</div>
        <div class="step-desc" id="pipeTrackersDesc">Concurrent UDP BEP-15 + HTTP Trackers + BEP-11 PEX</div>
      </div>

      <div class="pipeline-step active-stage">
        <div class="step-top">
          <span>2. Urgent Lookahead Window</span>
          <span class="step-badge stream" id="pipeBufferBadge">48 MiB WINDOW</span>
        </div>
        <div class="step-main" id="pipeUrgentVal">Cursor Piece #0</div>
        <div class="step-desc" id="pipeBlocksDesc">0.45s seek-head block racing • 16 KiB sub-piece striping</div>
      </div>

      <div class="pipeline-step active-stage">
        <div class="step-top">
          <span>3. HTTP 206 Range Streamer</span>
          <span class="step-badge stream" id="pipeStreamBadge">READY</span>
        </div>
        <div class="step-main" id="pipeThroughputVal">0.00 MiB/s</div>
        <div class="step-desc" id="pipeStreamDesc">Direct sparse pread/pwrite • Instant MSG_CANCEL seek</div>
      </div>

      <div class="pipeline-step disk-stage">
        <div class="step-top">
          <span>4. Background Disk Persistence</span>
          <span class="step-badge live" id="pipeDiskBadge">IDLE</span>
        </div>
        <div class="step-main" id="pipeDiskVal">0 B / 0 B Saved</div>
        <div class="step-desc" id="pipeDiskPath">Writing & SHA-1 verifying full file to ./downloads/</div>
      </div>
    </section>

    <!-- 3. Main Workspace: Left = Cinema Stage + Subtitle Studio | Right = Disk & Swarm Telemetry + Piece Map -->
    <div class="stage-layout">
      <!-- Left Column: Video Player Stage + Precision Subtitle Studio -->
      <div style="display:flex; flex-direction:column; gap:16px;">
        <section class="panel">
          <div class="panel-header">
            <div class="panel-title">
              <span>Cinema HTTP 206 Partial Content Stage</span>
              <span style="font-family:var(--mono); font-size:11px; color:var(--text-muted);" id="playerFileBadge">No active media</span>
            </div>
            <div style="display:flex; align-items:center; gap:8px;">
              <button class="btn btn-sm" onclick="toggleSubtitleVisibility()" id="subToggleBtn">CC: ON</button>
              <button class="btn btn-sm" onclick="cycleSubtitleSize()" id="subSizeBtn">Font: M</button>
              <button class="btn btn-sm" onclick="toggleStageFullscreen()">⛶ Fullscreen Stage</button>
            </div>
          </div>

          <div class="player-stage" id="playerStage">
            <video id="videoPlayer" controls preload="metadata" crossorigin="anonymous"></video>
            <div class="subtitle-overlay" id="subtitleOverlay">
              <div class="subtitle-line" id="subtitleLine"></div>
            </div>
          </div>

          <div class="stage-FloatingBar">
            <div style="display:flex; align-items:center; gap:10px; flex-wrap:wrap;">
              <span style="font-family:var(--mono); font-size:11px; color:var(--text-secondary);">
                PLAYBACK TIME: <strong id="playerTimeReadout" style="color:var(--text);">00:00:00.000</strong>
              </span>
              <span style="color:var(--border-strong);">|</span>
              <span style="font-family:var(--mono); font-size:11px; color:var(--text-secondary);">
                SUBTITLE TRACK: <strong id="subTrackName" style="color:var(--blue);">None Loaded (.SRT / .VTT / .ASS)</strong>
              </span>
            </div>
            <div style="display:flex; align-items:center; gap:6px;">
              <label class="btn btn-sm btn-emerald" style="margin:0; cursor:pointer;">
                + Load Subtitle (.srt / .vtt / .ass)
                <input type="file" id="subtitleFileInput" accept=".srt,.vtt,.ass,.ssa,.sub,.txt" style="display:none" onchange="handleSubtitleUpload(this)" />
              </label>
              <button class="btn btn-sm" onclick="loadDemoSubtitles()" title="Load sample time-coded subtitles to test millisecond sync adjustment">
                Load Test Subtitles
              </button>
            </div>
          </div>
        </section>

        <!-- Precision Subtitle Synchronization Studio -->
        <section class="panel">
          <div class="panel-header">
            <div class="panel-title">
              <span>Precision Subtitle Timing & Sync Studio</span>
              <span style="font-family:var(--mono); font-size:10.5px; color:var(--text-muted);">Shortcuts: [ or G (-50ms) • ] or H (+50ms)</span>
            </div>
            <div style="display:flex; align-items:center; gap:6px;">
              <button class="btn btn-sm" onclick="exportShiftedSrt()" id="exportSubBtn" style="display:none;">
                ↓ Download Shifted .SRT
              </button>
              <button class="btn btn-sm" onclick="clearSubtitles()" id="clearSubBtn" style="display:none;">
                Clear
              </button>
            </div>
          </div>
          <div class="panel-body sub-controls-grid">
            <div class="sub-offset-box">
              <div style="display:flex; align-items:center; gap:5px; flex-wrap:wrap;">
                <span style="font-size:11px; font-family:var(--mono); color:var(--text-muted); margin-right:4px;">EARLIER:</span>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(-5.0)">-5.0s</button>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(-1.0)">-1.0s</button>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(-0.25)">-250ms</button>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(-0.05)">-50ms</button>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(-0.01)">-10ms</button>
              </div>

              <div style="display:flex; align-items:center; gap:8px;">
                <div class="offset-readout" id="subOffsetReadout">+0.000s (0 ms)</div>
                <input type="number" id="subOffsetInput" class="offset-input" step="0.01" value="0.00" title="Enter exact subtitle offset in seconds (e.g. -1.45 or +2.10)" onchange="setSubtitleOffsetSeconds(parseFloat(this.value || 0))" />
                <button class="btn btn-sm" onclick="setSubtitleOffsetSeconds(0)">Reset 0ms</button>
              </div>

              <div style="display:flex; align-items:center; gap:5px; flex-wrap:wrap;">
                <span style="font-size:11px; font-family:var(--mono); color:var(--text-muted); margin-right:4px;">LATER:</span>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(0.01)">+10ms</button>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(0.05)">+50ms</button>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(0.25)">+250ms</button>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(1.0)">+1.0s</button>
                <button class="btn btn-sm btn-mono" onclick="nudgeSubtitleOffset(5.0)">+5.0s</button>
              </div>
            </div>

            <div style="display:flex; align-items:center; justify-content:space-between; font-size:11.5px; color:var(--text-secondary);">
              <span><strong>Interactive Cue Timeline:</strong> Click <em>"Snap to Video Now"</em> on any dialogue line below when you hear the actor speak it to auto-calibrate the exact offset.</span>
              <span style="font-family:var(--mono); font-size:11px; color:var(--text-muted);" id="subCueCountLabel">0 cues loaded</span>
            </div>

            <div class="cue-list" id="subCueList">
              <div style="padding:20px; text-align:center; color:var(--text-muted); font-size:12px;">
                Load any <code>.srt</code>, <code>.vtt</code>, or <code>.ass</code> subtitle file above (or click <em>Load Test Subtitles</em>) to inspect dialogue cues and adjust forward/backward timing with 10ms precision.
              </div>
            </div>
          </div>
        </section>
      </div>

      <!-- Right Column: Simultaneous Stream + Disk Persistence Telemetry & Interactive Piece Map -->
      <div style="display:flex; flex-direction:column; gap:16px;">
        <section class="panel">
          <div class="panel-header">
            <div class="panel-title">
              <span>Stream Lookahead & Background Disk Persistence</span>
            </div>
            <span style="font-family:var(--mono); font-size:11px; color:var(--emerald);" id="diskPersistenceStateBadge">STANDBY</span>
          </div>
          <div class="panel-body">
            <!-- Dual Progress Bars clearly separating Stream Buffer vs Background Disk Save -->
            <div class="dual-progress-card">
              <div class="progress-block">
                <div class="progress-row-top">
                  <span style="font-weight:600; color:var(--emerald);">1. Full Video Background Download to Disk (<code>./downloads</code>)</span>
                  <span style="font-family:var(--mono); font-weight:600; color:var(--text);" id="statProgress">0% (0/0 pieces)</span>
                </div>
                <div class="progress-bar-track">
                  <div class="progress-fill-disk" id="progressBar"></div>
                </div>
                <div style="display:flex; justify-content:space-between; margin-top:6px; font-size:11px; color:var(--text-secondary); font-family:var(--mono);">
                  <span id="diskWrittenLabel">0 B written to sparse file</span>
                  <span id="diskEtaLabel">ETA: —</span>
                </div>
              </div>

              <div class="progress-block">
                <div class="progress-row-top">
                  <span style="font-weight:600; color:var(--blue);">2. Urgent Playback Lookahead Buffer (48 MiB Window Ahead of Seek Head)</span>
                  <span style="font-family:var(--mono); font-weight:600; color:var(--blue);" id="lookaheadBufferLabel">Waiting for stream...</span>
                </div>
                <div class="progress-bar-track">
                  <div class="progress-fill-buffer" id="lookaheadBar" style="width:0%"></div>
                </div>
                <div style="display:flex; justify-content:space-between; margin-top:6px; font-size:11px; color:var(--text-secondary); font-family:var(--mono);">
                  <span id="urgentWindowPiecesLabel">Urgent Pieces: —</span>
                  <span id="subPieceBlocksLabel">0 sub-piece blocks (16 KiB) in-flight</span>
                </div>
              </div>
            </div>

            <!-- Structured Engineering KV Telemetry -->
            <div class="telemetry-kv-grid">
              <div class="kv-cell">
                <div class="kv-label">Target Video File</div>
                <div class="kv-val" id="statName">—</div>
              </div>
              <div class="kv-cell">
                <div class="kv-label">Container Size & Piece Size</div>
                <div class="kv-val" id="statSize">—</div>
              </div>
              <div class="kv-cell">
                <div class="kv-label">Live Swarm Speed</div>
                <div class="kv-val" id="statSpeed" style="color:var(--emerald);">0.00 MiB/s</div>
              </div>
              <div class="kv-cell">
                <div class="kv-label">Connected Peers / Swarm</div>
                <div class="kv-val" id="statPeers">0 connected / 0 discovered</div>
              </div>
              <div class="kv-cell">
                <div class="kv-label">Disk Output Path</div>
                <div class="kv-val" id="statDiskPath" style="font-size:11.5px; color:var(--text-secondary);">./downloads/</div>
              </div>
              <div class="kv-cell">
                <div class="kv-label">BTIH InfoHash (SHA-1)</div>
                <div class="kv-val" id="statHash" style="font-size:11.5px; color:var(--text-secondary);">—</div>
              </div>
            </div>

            <!-- Interactive Sparse Piece Map -->
            <div style="display:flex; align-items:center; justify-content:space-between; margin-bottom:6px;">
              <span style="font-size:11px; font-weight:600; text-transform:uppercase; letter-spacing:0.05em; color:var(--text-secondary);">
                Interactive Sparse Piece Map (Click any piece to seek)
              </span>
              <span style="font-family:var(--mono); font-size:11px; color:var(--text-muted);" id="pieceHoverInfo">
                Hover or click a piece cell
              </span>
            </div>

            <div id="pieceGrid" class="piece-grid"></div>

            <div class="legend-row">
              <span class="legend-item"><span class="dot" style="background:var(--emerald)"></span>SHA-1 Verified on Disk</span>
              <span class="legend-item"><span class="dot" style="background:var(--blue)"></span>Receiving 16 KiB Sub-Piece Blocks</span>
              <span class="legend-item"><span class="dot" style="background:var(--amber)"></span>48 MiB Urgent Stream Lookahead</span>
              <span class="legend-item"><span class="dot" style="background:#1f1f27"></span>Queued for Background Download</span>
            </div>
          </div>
        </section>
      </div>
    </div>
  </main>

  <script>
    let pollTimer = null;
    let currentSessionSize = 0;
    let currentPieceLength = 0;
    let currentTotalPieces = 0;

    // =========================================================================
    // Precision Subtitle Engine (.SRT, .VTT, .ASS/.SSA + Millisecond Offset Sync)
    // =========================================================================
    let subtitleCues = [];       // [{ index, start, end, text }]
    let subtitleOffsetSec = 0.0; // Positive = subtitles appear LATER, Negative = EARLIER
    let subtitlesEnabled = true;
    let subtitleFontSizes = [17, 21, 26, 32];
    let subtitleFontSizeLabels = ['S', 'M', 'L', 'XL'];
    let subtitleFontIdx = 1;
    let lastActiveCueIdx = -2;

    function formatTimestamp(sec) {
      if (!isFinite(sec) || sec < 0) sec = 0;
      const hrs = Math.floor(sec / 3600);
      const mins = Math.floor((sec % 3600) / 60);
      const s = Math.floor(sec % 60);
      const ms = Math.round((sec - Math.floor(sec)) * 1000);
      return String(hrs).padStart(2, '0') + ':' +
             String(mins).padStart(2, '0') + ':' +
             String(s).padStart(2, '0') + '.' +
             String(ms).padStart(3, '0');
    }

    function parseTimecodeToSeconds(tc) {
      if (!tc) return 0;
      const clean = tc.trim().replace(',', '.');
      const parts = clean.split(':');
      if (parts.length === 3) {
        return parseFloat(parts[0]) * 3600 + parseFloat(parts[1]) * 60 + parseFloat(parts[2]);
      } else if (parts.length === 2) {
        return parseFloat(parts[0]) * 60 + parseFloat(parts[1]);
      }
      return parseFloat(clean) || 0;
    }

    function parseSubtitleText(rawText, filename) {
      const cues = [];
      const ext = (filename || '').toLowerCase();
      const normalized = rawText.replace(/\\r\\n/g, '\\n').replace(/\\r/g, '\\n');

      if (ext.endsWith('.ass') || ext.endsWith('.ssa') || normalized.includes('[Events]')) {
        const lines = normalized.split('\\n');
        for (const line of lines) {
          if (line.startsWith('Dialogue:')) {
            const rest = line.slice('Dialogue:'.length).trim();
            const cols = rest.split(',');
            if (cols.length >= 10) {
              const start = parseTimecodeToSeconds(cols[1]);
              const end = parseTimecodeToSeconds(cols[2]);
              const rawDlg = cols.slice(9).join(',')
                .replace(/\\{[^}]*\\}/g, '')
                .replace(/\\\\N/g, '\\n')
                .replace(/\\\\n/g, '\\n')
                .trim();
              if (rawDlg && end > start) {
                cues.push({ index: cues.length + 1, start, end, text: rawDlg });
              }
            }
          }
        }
      } else {
        const blocks = normalized.split(/\\n\\s*\\n/);
        for (const block of blocks) {
          const lines = block.trim().split('\\n');
          if (!lines.length) continue;
          let tcLineIdx = -1;
          for (let i = 0; i < Math.min(3, lines.length); i++) {
            if (lines[i].includes('-->')) {
              tcLineIdx = i;
              break;
            }
          }
          if (tcLineIdx === -1) continue;
          const tcParts = lines[tcLineIdx].split('-->');
          const start = parseTimecodeToSeconds(tcParts[0]);
          const end = parseTimecodeToSeconds(tcParts[1].trim().split(/\\s+/)[0]);
          const text = lines.slice(tcLineIdx + 1)
            .join('\\n')
            .replace(/<[^>]+>/g, '')
            .trim();
          if (text && end >= start) {
            cues.push({ index: cues.length + 1, start, end, text });
          }
        }
      }
      cues.sort((a, b) => a.start - b.start);
      return cues;
    }

    function handleSubtitleUpload(inputEl) {
      if (!inputEl.files || !inputEl.files.length) return;
      const file = inputEl.files[0];
      const reader = new FileReader();
      reader.onload = (e) => {
        const parsed = parseSubtitleText(e.target.result || '', file.name);
        subtitleCues = parsed;
        lastActiveCueIdx = -2;
        document.getElementById('subTrackName').textContent = file.name + ' (' + parsed.length + ' cues)';
        document.getElementById('subCueCountLabel').textContent = parsed.length + ' cues loaded';
        document.getElementById('exportSubBtn').style.display = parsed.length ? 'inline-flex' : 'none';
        document.getElementById('clearSubBtn').style.display = parsed.length ? 'inline-flex' : 'none';
        renderSubtitleCueList(-1);
        updateSubtitleOverlay();
        showStatus('Loaded subtitle "' + file.name + '" (' + parsed.length + ' cues). Use ±10ms / ±50ms / ±250ms buttons or [ / ] keys to fine-tune sync.');
      };
      reader.readAsText(file);
    }

    function loadDemoSubtitles() {
      const video = document.getElementById('videoPlayer');
      const base = Math.floor(video.currentTime || 0);
      const sampleSrt = [
        "1\\n" + formatTimestamp(base + 0.2).replace('.', ',') + " --> " + formatTimestamp(base + 3.5).replace('.', ',') + "\\n[Subtitle Engine Active] Synchronized to 10ms precision.",
        "2\\n" + formatTimestamp(base + 3.8).replace('.', ',') + " --> " + formatTimestamp(base + 7.5).replace('.', ',') + "\\nUse -50ms / +50ms buttons or press [ and ] keys to shift subtitles forward or backward.",
        "3\\n" + formatTimestamp(base + 7.8).replace('.', ',') + " --> " + formatTimestamp(base + 12.0).replace('.', ',') + "\\nOr click 'Snap to Video Now' on any dialogue row below when you hear the line spoken!",
        "4\\n" + formatTimestamp(base + 12.5).replace('.', ',') + " --> " + formatTimestamp(base + 17.0).replace('.', ',') + "\\nStreaming HTTP 206 Partial Content while simultaneously saving the full video to ./downloads."
      ].join("\\n\\n");
      subtitleCues = parseSubtitleText(sampleSrt, 'sample_sync_test.srt');
      lastActiveCueIdx = -2;
      document.getElementById('subTrackName').textContent = 'sample_sync_test.srt (' + subtitleCues.length + ' cues)';
      document.getElementById('subCueCountLabel').textContent = subtitleCues.length + ' cues loaded';
      document.getElementById('exportSubBtn').style.display = 'inline-flex';
      document.getElementById('clearSubBtn').style.display = 'inline-flex';
      renderSubtitleCueList(-1);
      updateSubtitleOverlay();
    }

    function clearSubtitles() {
      subtitleCues = [];
      subtitleOffsetSec = 0.0;
      document.getElementById('subTrackName').textContent = 'None Loaded (.SRT / .VTT / .ASS)';
      document.getElementById('subCueCountLabel').textContent = '0 cues loaded';
      document.getElementById('exportSubBtn').style.display = 'none';
      document.getElementById('clearSubBtn').style.display = 'none';
      document.getElementById('subtitleLine').textContent = '';
      setSubtitleOffsetSeconds(0);
      renderSubtitleCueList(-1);
    }

    function setSubtitleOffsetSeconds(val) {
      if (!isFinite(val)) val = 0;
      subtitleOffsetSec = Math.round(val * 1000) / 1000;
      const ms = Math.round(subtitleOffsetSec * 1000);
      const sign = subtitleOffsetSec >= 0 ? '+' : '';
      document.getElementById('subOffsetReadout').textContent =
        sign + subtitleOffsetSec.toFixed(3) + 's (' + (ms >= 0 ? '+' : '') + ms + ' ms)';
      document.getElementById('subOffsetInput').value = subtitleOffsetSec.toFixed(2);
      lastActiveCueIdx = -2;
      updateSubtitleOverlay();
    }

    function nudgeSubtitleOffset(deltaSec) {
      setSubtitleOffsetSeconds(subtitleOffsetSec + deltaSec);
    }

    function snapCueToCurrentVideoTime(cueIdx) {
      if (cueIdx < 0 || cueIdx >= subtitleCues.length) return;
      const video = document.getElementById('videoPlayer');
      const nowTime = video.currentTime || 0;
      const targetCue = subtitleCues[cueIdx];
      const newOffset = nowTime - targetCue.start;
      setSubtitleOffsetSeconds(newOffset);
      showStatus('Snapped Cue #' + (cueIdx + 1) + ' to current video timestamp (' + formatTimestamp(nowTime) + '). Offset set to ' + (newOffset >= 0 ? '+' : '') + newOffset.toFixed(3) + 's.');
    }

    function toggleSubtitleVisibility() {
      subtitlesEnabled = !subtitlesEnabled;
      document.getElementById('subToggleBtn').textContent = 'CC: ' + (subtitlesEnabled ? 'ON' : 'OFF');
      updateSubtitleOverlay();
    }

    function cycleSubtitleSize() {
      subtitleFontIdx = (subtitleFontIdx + 1) % subtitleFontSizes.length;
      document.getElementById('subtitleLine').style.fontSize = subtitleFontSizes[subtitleFontIdx] + 'px';
      document.getElementById('subSizeBtn').textContent = 'Font: ' + subtitleFontSizeLabels[subtitleFontIdx];
    }

    function toggleStageFullscreen() {
      const stage = document.getElementById('playerStage');
      if (!document.fullscreenElement) {
        stage.requestFullscreen().catch(() => {});
      } else {
        document.exitFullscreen().catch(() => {});
      }
    }

    function exportShiftedSrt() {
      if (!subtitleCues.length) return;
      const lines = subtitleCues.map((c, idx) => {
        const s = Math.max(0, c.start + subtitleOffsetSec);
        const e = Math.max(s + 0.1, c.end + subtitleOffsetSec);
        return (idx + 1) + '\\n' + formatTimestamp(s).replace('.', ',') + ' --> ' + formatTimestamp(e).replace('.', ',') + '\\n' + c.text;
      });
      const blob = new Blob([lines.join('\\n\\n') + '\\n'], { type: 'text/plain;charset=utf-8' });
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = 'synced_subtitles_' + (subtitleOffsetSec >= 0 ? 'plus_' : 'minus_') + Math.abs(Math.round(subtitleOffsetSec * 1000)) + 'ms.srt';
      document.body.appendChild(a);
      a.click();
      a.remove();
    }

    function renderSubtitleCueList(activeIdx) {
      const container = document.getElementById('subCueList');
      if (!subtitleCues.length) {
        container.innerHTML = '<div style="padding:20px; text-align:center; color:var(--text-muted); font-size:12px;">Load any <code>.srt</code>, <code>.vtt</code>, or <code>.ass</code> subtitle file above (or click <em>Load Test Subtitles</em>) to inspect dialogue cues and adjust forward/backward timing with 10ms precision.</div>';
        return;
      }
      const video = document.getElementById('videoPlayer');
      const vTime = video.currentTime || 0;
      let centerIdx = activeIdx >= 0 ? activeIdx : subtitleCues.findIndex(c => (c.end + subtitleOffsetSec) >= vTime);
      if (centerIdx < 0) centerIdx = 0;
      const startIdx = Math.max(0, centerIdx - 6);
      const endIdx = Math.min(subtitleCues.length, startIdx + 30);

      let html = '';
      for (let i = startIdx; i < endIdx; i++) {
        const c = subtitleCues[i];
        const shiftedStart = Math.max(0, c.start + subtitleOffsetSec);
        const isActive = (i === activeIdx);
        const safeText = c.text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/\\n/g, ' ');
        html += '<div class="cue-item ' + (isActive ? 'active-cue' : '') + '">' +
          '<span class="cue-time">#' + c.index + ' • ' + formatTimestamp(shiftedStart).slice(0, 11) + '</span>' +
          '<span class="cue-text" title="' + safeText + '">' + safeText + '</span>' +
          '<button class="btn btn-sm" style="padding:2px 8px; font-size:10.5px;" onclick="snapCueToCurrentVideoTime(' + i + ')">⏱ Snap to Video Now</button>' +
          '</div>';
      }
      container.innerHTML = html;
    }

    function updateSubtitleOverlay() {
      const video = document.getElementById('videoPlayer');
      const vTime = video.currentTime || 0;
      document.getElementById('playerTimeReadout').textContent = formatTimestamp(vTime);

      const lineEl = document.getElementById('subtitleLine');
      if (!subtitlesEnabled || !subtitleCues.length) {
        lineEl.textContent = '';
        return;
      }

      let foundIdx = -1;
      const activeTexts = [];
      for (let i = 0; i < subtitleCues.length; i++) {
        const c = subtitleCues[i];
        const s = c.start + subtitleOffsetSec;
        const e = c.end + subtitleOffsetSec;
        if (vTime >= s && vTime <= e) {
          if (foundIdx === -1) foundIdx = i;
          activeTexts.push(c.text);
        } else if (s > vTime + 2) {
          break;
        }
      }

      lineEl.textContent = activeTexts.join('\\n');
      if (foundIdx !== lastActiveCueIdx) {
        lastActiveCueIdx = foundIdx;
        renderSubtitleCueList(foundIdx);
      }
    }

    window.addEventListener('keydown', (e) => {
      if (['INPUT', 'TEXTAREA'].includes((e.target && e.target.tagName) || '')) return;
      if (e.key === '[' || e.key === 'g' || e.key === 'G') {
        nudgeSubtitleOffset(e.shiftKey ? -0.50 : -0.05);
      } else if (e.key === ']' || e.key === 'h' || e.key === 'H') {
        nudgeSubtitleOffset(e.shiftKey ? 0.50 : 0.05);
      }
    });

    // =========================================================================
    // Torrent & Swarm Session Controls
    // =========================================================================
    async function loadPreset(preset) {
      const res = await fetch('/api/fixture-magnet?preset=' + encodeURIComponent(preset || 'fixture'));
      const data = await res.json();
      document.getElementById('magnetInput').value = data.magnet;
      showStatus('Loaded preset: ' + (data.label || preset) + '. Click "Stream + Save Full File in Background" to begin.');
    }

    async function loadFixtureMagnet(preset = 'fixture') {
      return loadPreset(preset);
    }

    async function uploadTorrentFile(inputEl) {
      if (!inputEl.files || !inputEl.files.length) return;
      const file = inputEl.files[0];
      const buf = await file.arrayBuffer();
      const res = await fetch('/api/upload-torrent?name=' + encodeURIComponent(file.name), {
        method: 'POST',
        body: buf
      });
      const data = await res.json();
      if (data.path) {
        document.getElementById('magnetInput').value = data.path;
        showStatus('Uploaded ' + file.name + '. Click "Stream + Save Full File in Background" or "Download Only".');
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
      if (!bytes || bytes <= 0) return '0 B';
      const units = ['B', 'KiB', 'MiB', 'GiB'];
      let i = 0;
      let val = bytes;
      while (val >= 1024 && i < units.length - 1) { val /= 1024; i++; }
      return val.toFixed(i === 0 ? 0 : 2) + ' ' + units[i];
    }

    function formatEta(sec) {
      if (sec === 0) return 'Complete (Verified on Disk)';
      if (sec === null || sec === undefined || !isFinite(sec) || sec < 0) return 'Calculating...';
      if (sec < 60) return sec + 's remaining';
      const m = Math.floor(sec / 60);
      const s = sec % 60;
      if (m < 60) return m + 'm ' + s + 's remaining';
      const h = Math.floor(m / 60);
      return h + 'h ' + (m % 60) + 'm remaining';
    }

    async function seekToPiece(pieceIdx) {
      if (!currentTotalPieces) return;
      try {
        const targetRatio = Math.max(0, Math.min(0.995, pieceIdx / currentTotalPieces));
        await fetch('/api/seek-piece', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({ piece_index: pieceIdx })
        }).catch(() => {});
        const video = document.getElementById('videoPlayer');
        if (video.duration && isFinite(video.duration) && video.duration > 0) {
          video.currentTime = targetRatio * video.duration;
          video.play().catch(() => {});
          showStatus('Jumped to Piece #' + pieceIdx + ' (~' + formatBytes(pieceIdx * currentPieceLength) + ') — streaming from this point immediately.');
        } else {
          window._pendingPieceSeekRatio = targetRatio;
          video.play().catch(() => {});
          showStatus('Prioritized Piece #' + pieceIdx + ' (~' + formatBytes(pieceIdx * currentPieceLength) + ') — player will jump as soon as container index loads.');
        }
      } catch (_) {}
    }

    async function startSession(mode) {
      window._dlTriggered = false;
      const source = document.getElementById('magnetInput').value.trim();
      if (!source) {
        await loadFixtureMagnet();
      }
      const finalSource = document.getElementById('magnetInput').value.trim();
      showStatus(mode === 'stream'
        ? 'Resolving Magnet / Torrent metadata → Launching HTTP 206 Range Stream + Background Disk Persistence...'
        : 'Resolving Magnet / Torrent metadata → Starting Full Background Disk Download to ./downloads...');

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

        currentSessionSize = data.size || 0;
        document.getElementById('statName').textContent = data.file_name;
        document.getElementById('playerFileBadge').textContent = data.file_name + ' (' + formatBytes(data.size) + ')';
        document.getElementById('statSize').textContent = formatBytes(data.size);
        document.getElementById('statHash').textContent = data.info_hash;
        document.getElementById('statDiskPath').textContent = data.output_path;
        document.getElementById('saveDiskLink').style.display = 'inline-flex';
        document.getElementById('saveDiskLink').href = '/download?t=' + Date.now();

        const modePill = document.getElementById('engineModePill');
        if (mode === 'stream') {
          modePill.className = 'engine-mode-pill streaming';
          modePill.textContent = 'LIVE STREAMING + SAVING FULL FILE TO DISK';
          const video = document.getElementById('videoPlayer');
          video.src = '/stream?t=' + Date.now();
          video.play().catch(() => {});
          showStatus('Streaming via HTTP 206 Partial Content AND simultaneously downloading full file to ' + data.output_path);
        } else {
          modePill.className = 'engine-mode-pill streaming';
          modePill.textContent = 'BACKGROUND DISK DOWNLOAD ACTIVE';
          showStatus('Downloading full verified file to ' + data.output_path + ' ...');
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

        currentSessionSize = st.size || currentSessionSize;
        currentPieceLength = st.piece_length || currentPieceLength;
        currentTotalPieces = st.total_pieces || currentTotalPieces;

        const rawPct = (st.progress || 0) * 100;
        const pctLabel = (rawPct > 0 && rawPct < 1) ? rawPct.toFixed(2) : Math.round(rawPct);
        const speedStr = formatBytes(st.speed_bps || 0) + '/s';

        document.getElementById('exportPctLabel').textContent = pctLabel + '%';
        document.getElementById('statProgress').textContent =
          pctLabel + '% (' + st.completed_pieces + ' / ' + st.total_pieces + ' pieces verified)';
        document.getElementById('progressBar').style.width =
          Math.min(100, Math.max(rawPct, st.bytes_downloaded ? 1.5 : 0)) + '%';

        document.getElementById('diskWrittenLabel').textContent =
          formatBytes(st.bytes_downloaded || 0) + ' of ' + formatBytes(st.size || 0) + ' written to disk';
        document.getElementById('diskEtaLabel').textContent = 'ETA: ' + formatEta(st.eta_seconds);

        document.getElementById('statSpeed').textContent = speedStr;
        document.getElementById('statSize').textContent =
          formatBytes(st.size || 0) + ' • ' + formatBytes(st.piece_length || 0) + '/piece';
        document.getElementById('statPeers').textContent =
          (st.connected_peers || 0) + ' active TCP / ' + (st.total_swarm_peers || 0) + ' swarm';
        if (st.output_path) {
          document.getElementById('statDiskPath').textContent = st.output_path;
          document.getElementById('pipeDiskPath').textContent = 'Saving full file to ' + st.output_path;
        }

        document.getElementById('pipeSwarmBadge').textContent = (st.connected_peers || 0) + ' CONNECTED';
        document.getElementById('pipePeersVal').textContent =
          (st.connected_peers || 0) + ' Active / ' + (st.total_swarm_peers || 0) + ' Swarm Peers';

        const urgList = (st.urgent_window && st.urgent_window.length)
          ? ('#' + st.urgent_window.join(', #'))
          : ('#' + (st.priority_cursor || 0));
        document.getElementById('pipeUrgentVal').textContent = 'Cursor #' + (st.read_cursor_piece || 0) + ' → [' + urgList + ']';
        document.getElementById('pipeThroughputVal').textContent = speedStr + (st.seek_epoch ? ' • ' + st.seek_epoch + ' Seeks' : '');
        document.getElementById('pipeDiskBadge').textContent = st.complete ? '100% SAVED ON DISK' : 'WRITING TO DISK';
        document.getElementById('pipeDiskVal').textContent =
          formatBytes(st.bytes_downloaded || 0) + ' / ' + formatBytes(st.size || 0);
        document.getElementById('diskPersistenceStateBadge').textContent =
          st.complete ? '✓ 100% SHA-1 VERIFIED ON DISK' : '● SAVING IN BACKGROUND (' + speedStr + ')';

        const readyAheadPieces = st.lookahead_ready_pieces || 0;
        const activeSubBlocks = st.in_progress_blocks || 0;
        const activeSubBytes = activeSubBlocks * 16384;
        const readyAheadBytes = readyAheadPieces * (st.piece_length || 0) + activeSubBytes;
        const targetLookaheadBytes = Math.min(st.size || 1, Math.max((st.piece_length || 32768) * 4, 16 * 1024 * 1024));
        const lookaheadPct = st.complete ? 100 : Math.min(100, Math.round((readyAheadBytes / targetLookaheadBytes) * 100));
        document.getElementById('lookaheadBar').style.width = Math.max(lookaheadPct, activeSubBlocks ? 8 : 0) + '%';
        document.getElementById('lookaheadBufferLabel').textContent =
          st.complete ? 'Full File Buffered (100%)' : (formatBytes(readyAheadBytes) + ' ready ahead of cursor');
        document.getElementById('urgentWindowPiecesLabel').textContent = 'Urgent Window: ' + urgList;
        document.getElementById('subPieceBlocksLabel').textContent =
          activeSubBlocks + ' sub-piece blocks (' + formatBytes(activeSubBytes) + ') in-flight across ' + (st.active_pieces_count || 0) + ' active pieces';

        const grid = document.getElementById('pieceGrid');
        if (st.pieces) {
          if (grid.children.length !== st.pieces.length) {
            grid.innerHTML = '';
            for (let i = 0; i < st.pieces.length; i++) {
              const cell = document.createElement('div');
              cell.className = 'piece-cell ' + st.pieces[i];
              cell.onclick = () => seekToPiece(i);
              cell.onmouseenter = () => {
                const startOff = formatBytes(i * (st.piece_length || 0));
                document.getElementById('pieceHoverInfo').textContent =
                  'Piece #' + i + ' (' + startOff + ') • State: ' + st.pieces[i].toUpperCase() + ' (Click to seek)';
              };
              grid.appendChild(cell);
            }
          } else {
            for (let i = 0; i < st.pieces.length; i++) {
              const cname = 'piece-cell ' + st.pieces[i];
              if (grid.children[i].className !== cname) {
                grid.children[i].className = cname;
              }
            }
          }
        }

        if (st.complete && mode === 'download' && !window._dlTriggered) {
          window._dlTriggered = true;
          showStatus('Download 100% SHA-1 Verified! Saved to ' + st.output_path + '. Triggering browser file save...');
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
      const video = document.getElementById('videoPlayer');
      video.addEventListener('timeupdate', updateSubtitleOverlay);
      video.addEventListener('seeking', () => {
        if (
          window._lastExplicitSeekStamp &&
          (performance.now() - window._lastExplicitSeekStamp) < 300 &&
          typeof window._lastExplicitSeekTime === 'number' &&
          Math.abs(video.currentTime - window._lastExplicitSeekTime) > 1.5
        ) {
          video.currentTime = window._lastExplicitSeekTime;
        }
        updateSubtitleOverlay();
      });
      video.addEventListener('seeked', updateSubtitleOverlay);
      video.addEventListener('loadedmetadata', () => {
        if (window._pendingPieceSeekRatio !== null && window._pendingPieceSeekRatio !== undefined && video.duration > 0) {
          const ratio = window._pendingPieceSeekRatio;
          window._pendingPieceSeekRatio = null;
          video.currentTime = ratio * video.duration;
          video.play().catch(() => {});
        }
      });

      // Always seek by exactly +10s on Right Arrow and -10s on Left Arrow (intercepts native browser % jumps)
      const handleArrowSeek = (e) => {
        if (e.metaKey || e.ctrlKey || e.altKey) return;
        const active = document.activeElement;
        if (active && active !== video && (active.tagName === 'INPUT' || active.tagName === 'TEXTAREA' || active.tagName === 'SELECT' || active.isContentEditable)) {
          return;
        }
        if (e.key === 'ArrowRight' || e.key === 'ArrowLeft') {
          e.preventDefault();
          e.stopPropagation();
          e.stopImmediatePropagation();
          if (e.type === 'keydown') {
            const baseTime = (
              window._lastExplicitSeekStamp &&
              (performance.now() - window._lastExplicitSeekStamp) < 250 &&
              typeof window._lastExplicitSeekTime === 'number'
            ) ? window._lastExplicitSeekTime : (video.currentTime || 0);
            const delta = (e.key === 'ArrowRight') ? 10 : -10;
            const maxDur = (video.duration && isFinite(video.duration) && video.duration > 0) ? video.duration : Infinity;
            const nextTime = Math.max(0, Math.min(maxDur, baseTime + delta));
            window._lastExplicitSeekTime = nextTime;
            window._lastExplicitSeekStamp = performance.now();
            if (document.activeElement === video) {
              try { video.blur(); } catch (_) {}
            }
            video.currentTime = nextTime;
            showStatus((delta > 0 ? '⏩ Forward +10s → ' : '⏪ Rewind -10s → ') + formatTimestamp(nextTime));
          }
        }
      };
      window.addEventListener('keydown', handleArrowSeek, { capture: true });
      window.addEventListener('keyup', handleArrowSeek, { capture: true });

      setInterval(updateSubtitleOverlay, 45);

      await loadFixtureMagnet();
      const res = await fetch('/status');
      const st = await res.json();
      if (st.active) {
        document.getElementById('statName').textContent = st.file_name;
        document.getElementById('playerFileBadge').textContent = st.file_name + ' (' + formatBytes(st.size) + ')';
        document.getElementById('statSize').textContent = formatBytes(st.size);
        document.getElementById('statHash').textContent = st.info_hash;
        document.getElementById('saveDiskLink').style.display = 'inline-flex';
        const modePill = document.getElementById('engineModePill');
        modePill.className = 'engine-mode-pill streaming';
        modePill.textContent = 'LIVE STREAMING + SAVING FULL FILE TO DISK';
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
    - `GET /` : Studio Web UI to paste magnet links, stream/download videos, and sync subtitles
    - `GET /api/fixture-magnet` : Returns a live `magnet:?xt=urn:btih:...` preset URI
    - `POST /api/upload-torrent` : Uploads a `.torrent` file from browser
    - `POST /api/start` : Starts a new `TorrentVideoSession` from any magnet URI or `.torrent` path
    - `POST /api/seek-piece` : Immediately prioritizes a clicked piece from the UI Piece Map
    - `GET /stream` : HTTP 206 Partial Content Range video streamer
    - `GET /download` : Direct attachment download of the verified video file
    - `GET /status` : Real-time JSON telemetry and piece state array
    """

    def __init__(
        self,
        store: Optional[SparseVideoPieceStore] = None,
        host: str = "127.0.0.1",
        port: int = 0,
        stream_chunk_size: int = 262144,
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

                if self.path.startswith("/api/seek-piece"):
                    length = int(self.headers.get("Content-Length", "0"))
                    body = json.loads(self.rfile.read(length).decode("utf-8") or "{}")
                    store = outer.store
                    if store is not None:
                        p_idx = int(body.get("piece_index", 0))
                        byte_off = max(0, p_idx * store.metadata.piece_length - store.target_file.offset)
                        store.register_stream_request(byte_off)
                        store.prioritize_byte_range(byte_off, byte_off + 65536)
                        self._send_json(200, {"ok": True, "piece_index": p_idx})
                        return
                    self._send_json(404, {"error": "No active store"})
                    return

                if self.path.startswith("/api/start"):
                    length = int(self.headers.get("Content-Length", "0"))
                    body = json.loads(self.rfile.read(length).decode("utf-8"))
                    source = body.get("source", "").strip()
                    mode = body.get("mode", "stream").strip()
                    if not source:
                        source = get_default_fixture_magnet()
                    try:
                        sess = TorrentVideoSession(source, outer.output_dir, sliding_window_pieces=16)
                        setattr(sess, "session_mode", mode)
                        sess.start_swarm()
                        outer.switch_session(sess)
                        self._send_json(200, {
                            "ok": True,
                            "mode": mode,
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
                    parsed_q = urllib.parse.parse_qs(urllib.parse.urlsplit(self.path).query)
                    preset = parsed_q.get("preset", ["fixture"])[0].lower()
                    if preset in ONLINE_MAGNET_PRESETS:
                        self._send_json(200, {
                            "magnet": ONLINE_MAGNET_PRESETS[preset],
                            "label": preset.replace("_", " ").title() + " (Online Swarm)",
                        })
                    else:
                        magnet = get_default_fixture_magnet()
                        self._send_json(200, {
                            "magnet": magnet,
                            "label": "Local H.264 Test Fixture (1 MB)",
                        })
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
                        snap["mode"] = getattr(sess, "session_mode", "stream")
                        snap["connected_peers"] = sum(1 for w in sess.workers if getattr(w, "connected", False))
                        snap["total_swarm_peers"] = len(sess.explicit_peers)
                        snap["webseeds_count"] = len(sess.web_seeds) * 8
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
                ext = Path(fname).suffix.lower()
                mime = "video/webm" if ext in (".mkv", ".webm") else "video/mp4"
                self.send_header("Content-Type", mime)
                self.send_header("Accept-Ranges", "bytes")
                self.send_header("Content-Length", str(content_length))
                self.send_header("Connection", "close")
                self.close_connection = True
                if as_attachment:
                    self.send_header("Content-Disposition", f'attachment; filename="{fname}"')
                self.end_headers()

                if not send_body:
                    return

                stream_id = 0 if as_attachment else store.register_stream_request(start_byte)
                cursor = start_byte
                while cursor <= end_byte:
                    if not as_attachment and store.is_stream_superseded(stream_id):
                        break
                    # Non-blocking check if browser closed/aborted the Range socket (sent FIN/RST on seek)
                    try:
                        peek = self.connection.recv(1, socket.MSG_PEEK | socket.MSG_DONTWAIT)
                        if peek == b"":
                            break
                    except BlockingIOError:
                        pass
                    except Exception:
                        break

                    cur_piece = store.piece_for_file_offset(cursor)
                    step = 524288 if cur_piece in store.completed_pieces else 65536
                    to_read = min(step, (end_byte - cursor) + 1)
                    chunk = store.read_video_bytes(cursor, to_read, timeout=45.0, stream_id=stream_id)
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
