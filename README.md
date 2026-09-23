# Torrent & Magnet Video Downloader + Streamer + Web UI

A zero-dependency Python 3 tool ([`torrent_video_tool.py`](file:///Users/aryankashyap/Downloads/Test/torrent_video_tool.py)) that downloads or streams **any size of video** from **Magnet links (`magnet:?xt=urn:btih:...`)** or `.torrent` files using BEP 0003 (BitTorrent Wire Protocol), BEP 0009/0010 (concurrent `ut_metadata` Magnet exchange), BEP 0015 (UDP Trackers), BEP 0005 (Mainline DHT), BEP 0019 (HTTP/HTTPS WebSeeds), and an HTTP `206 Partial Content` Range streaming server with an interactive Web UI.

## 1. Launch the Interactive Web UI (Paste Magnet Links to Stream or Download)
```bash
python3 torrent_video_tool.py ui --port 8080
```
Then open **[http://127.0.0.1:8080](http://127.0.0.1:8080)** in your browser:
- Paste any **`magnet:?xt=urn:btih:...`** link, or click any of the built-in preset buttons:
  - **🧪 Local H.264 Fixture (1 MB)**
  - **🎬 Sintel Online Magnet (129 MB)**
  - **🐰 Big Buck Bunny Online Magnet (263 MB)**
- Click **▶ Stream Video Now** to play immediately in the built-in HTML5 `<video>` player with arbitrary timeline seeking (`HTTP 206 Partial Content`) and a live **Sparse Piece Map Grid**.
- Click **⬇ Download Video** to verify all SHA-1 pieces and save the `.mp4` directly to disk (`./downloads/`) and your browser.

## 2. Verified Online Public-Domain Magnet Links
You can paste any of these verified Creative Commons / Blender Foundation Open Movie magnet links into the Web UI or pass them on the CLI:

- **Sintel (129.2 MB MP4, 987 pieces)**:
  ```text
  magnet:?xt=urn:btih:08ada5a7a6183aae1e09d831df6748d566095a10&dn=Sintel&tr=udp%3A%2F%2Ftracker.opentrackr.org%3A1337%2Fannounce&tr=udp%3A%2F%2Fopen.stealth.si%3A80%2Fannounce&tr=udp%3A%2F%2Fexodus.desync.com%3A6969%2Fannounce&ws=https%3A%2F%2Fwebtorrent.io%2Ftorrents%2F
  ```
- **Big Buck Bunny (276.1 MB MP4, 1,055 pieces)**:
  ```text
  magnet:?xt=urn:btih:dd8255ecdc7ca55fb0bbf81323d87062db1f6d1c&dn=Big+Buck+Bunny&tr=udp%3A%2F%2Ftracker.opentrackr.org%3A1337%2Fannounce&tr=udp%3A%2F%2Fopen.stealth.si%3A80%2Fannounce&tr=udp%3A%2F%2Fexodus.desync.com%3A6969%2Fannounce&ws=https%3A%2F%2Fwebtorrent.io%2Ftorrents%2F
  ```
- **Tears of Steel (571.3 MB WebM/MP4, 1,090 pieces)**:
  ```text
  magnet:?xt=urn:btih:209c8226b299b308beaf2b9cd3fb49212dbd13ec&dn=Tears+of+Steel&tr=udp%3A%2F%2Ftracker.opentrackr.org%3A1337%2Fannounce&tr=udp%3A%2F%2Fopen.stealth.si%3A80%2Fannounce&tr=udp%3A%2F%2Fexodus.desync.com%3A6969%2Fannounce&ws=https%3A%2F%2Fwebtorrent.io%2Ftorrents%2F
  ```

## 3. Run the End-to-End & Live Online Magnet Test Suite
```bash
python3 test_torrent_video_tool.py
```