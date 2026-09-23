# Torrent & Magnet Video Downloader + Streamer + Web UI

A zero-dependency Python 3 tool ([`torrent_video_tool.py`](file:///Users/aryankashyap/Downloads/Test/torrent_video_tool.py)) that downloads or streams **any size of video** from **Magnet links (`magnet:?xt=urn:btih:...`)** or `.torrent` files using BEP 0003 (BitTorrent Wire Protocol), BEP 0009/0010 (`ut_metadata` Magnet exchange), BEP 0015 (UDP Trackers), and an HTTP `206 Partial Content` Range streaming server with an interactive Web UI.

## 1. Launch the Interactive Web UI (Paste Magnet Links to Stream or Download)
```bash
python3 torrent_video_tool.py ui --port 8080
```
Then open **[http://127.0.0.1:8080](http://127.0.0.1:8080)** in your browser:
- Paste any **`magnet:?xt=urn:btih:...`** link (or click **🧪 Load Test Fixture Magnet Link** to load the built-in playable 640x360 H.264 MP4 magnet link).
- Click **▶ Stream Video Now** to play immediately in the built-in HTML5 `<video>` player with arbitrary timeline seeking (`HTTP 206 Partial Content`) and a live **Sparse Piece Map Grid**.
- Click **⬇ Download Video** to verify all SHA-1 pieces and save the `.mp4` directly to disk (`./downloads/`) and your browser.

## 2. CLI Usage (Stream or Download via Magnet Link or `.torrent`)
```bash
# Stream over HTTP (also serves the Web UI at http://127.0.0.1:8080/)
python3 torrent_video_tool.py stream path/to/video.torrent --port 8080 -o ./downloads

# Download a full video file
python3 torrent_video_tool.py download path/to/video.torrent -o ./downloads
```

## 3. Run the End-to-End Test Suite
```bash
python3 test_torrent_video_tool.py
```