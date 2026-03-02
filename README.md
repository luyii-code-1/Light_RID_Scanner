# Light RID Scanner

Lightweight OpenDroneID / Remote ID Wi-Fi scanner focused on long-running stability and practical field use.

- Runtime: terminal (`--no-tui`) + web UI
- Platform: Raspberry Pi / Linux monitor mode
- Parser: Beacon + Vendor IE + OpenDroneID Message Pack
- Persistence: history + track cache
- Notification: WeCom bot + optional browser notifications

## 中文说明

### 功能概览

- 实时接收并解析 OpenDroneID（RID）广播
- 网页端设备列表实时刷新，支持点击查看详情
- 地图默认仅显示无人机位置
- 仅在勾选设备后显示：
  - 飞手位置
  - 历史轨迹（淡蓝半透明线）
- 支持地图全屏，全屏下有迷你设备选择列表
- 历史与轨迹管理：
  - 删除指定飞机历史
  - 清空指定飞机轨迹
  - 清空全部轨迹
- 配置文件支持热保存（尽量不重启）

### 主要文件

- `run.py`：主程序（采集、解析、WebSocket、网页）
- `rid_config.example.json`：公开脱敏配置模板
- `rid_config.json`：本地实际配置（已在 `.gitignore` 忽略）
- `rid_models.json`：机型前缀映射

### 启动方式

```bash
sudo ~/rid/.venv/bin/python3 run.py --no-tui
```

网页地址：

- `http://<device-ip>:4600/`

### 新增接口（轨迹/历史管理）

- `GET /api/tracks/get?sn=<SN>`：获取指定飞机轨迹
- `POST /api/tracks/clear`：清空轨迹（可传 `sn`）
- `POST /api/history/delete`：删除指定飞机历史（传 `sn`）
- `POST /api/history/clear`：清空全部历史

## English

### Highlights

- Realtime OpenDroneID decoding from Wi-Fi management frames
- Web UI with live list, details card, AP panel, and map
- Aircraft markers shown by default
- Pilot marker + historical trajectory shown only for selected aircraft
- Fullscreen map mode with mini selection panel
- History/track maintenance APIs for long-running deployments

### Start

```bash
sudo ~/rid/.venv/bin/python3 run.py --no-tui
```

Open:

- `http://<device-ip>:4600/`

### API (Track / History)

- `GET /api/tracks/get?sn=<SN>`
- `POST /api/tracks/clear` (optional body: `{"sn":"..."}`)
- `POST /api/history/delete` (body: `{"sn":"..."}`)
- `POST /api/history/clear`

## Security

- Do not commit real `rid_config.json` with webhook keys.
- Keep secrets local; commit `rid_config.example.json` only.
