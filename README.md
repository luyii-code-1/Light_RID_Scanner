# Light RID Scanner

Lightweight OpenDroneID / Remote ID Wi-Fi scanner for Raspberry Pi and other Linux devices running monitor mode.  
Designed for long-running deployment with realtime Web UI, history retention, trajectory drawing, AP monitoring, and notifications.

## 中文说明

### 功能概览

- 实时接收并解析 OpenDroneID / Remote ID Wi-Fi Beacon
- 网页端显示实时设备列表、历史设备、AP 列表与地图
- 支持显示飞机位置、飞手位置、历史轨迹
- 支持历史与轨迹管理（删除、清空、导出）
- 支持企业微信机器人通知与浏览器通知
- 适合树莓派长期运行，可配合 `systemd` 守护

### 主要文件

- `run.py`：主程序（采集、解析、HTTP/WebSocket、前端页面）
- `rid_models.json`：机型前缀映射
- `rid_config.example.json`：脱敏配置模板（可提交）
- `rid_config.json`：本地实际配置（不要提交）

### 启动方式

```bash
sudo ~/rid/.venv/bin/python3 run.py --no-tui
```

网页地址：

- `http://<device-ip>:4600/`

### 配置与安全

- 部署时使用 `rid_config.json`
- 代码仓库仅保留 `rid_config.example.json`
- 企业微信 webhook key、本机 IP、私有路径等敏感信息请仅保存在本地

### 常用接口

- `GET /api/tracks/get?sn=<SN>`：获取单架飞机轨迹
- `POST /api/tracks/clear`：清空轨迹（可带 `{"sn":"..."}` 清空单架）
- `POST /api/history/delete`：删除单架历史
- `POST /api/history/clear`：清空全部历史
- `GET /api/config`：读取当前配置文本
- `POST /api/config/save`：保存并热重载配置

## English

### Highlights

- Realtime OpenDroneID / Remote ID decoding from Wi-Fi management frames
- Web UI with live aircraft list, AP list, details panel, and map
- Aircraft position, pilot position, and trajectory rendering
- History persistence and trajectory cache management
- WeCom bot notification and browser notification support
- Runtime control via configuration file
- Suitable for long-running Raspberry Pi deployment with `systemd`

### Main Files

- `run.py`: scanner, parser, HTTP/WebSocket server, and embedded frontend
- `rid_models.json`: aircraft model prefix map
- `rid_config.example.json`: sanitized configuration template
- `rid_config.json`: local runtime config (do not commit)

### Start

```bash
sudo ~/rid/.venv/bin/python3 run.py --no-tui
```

Open:

- `http://<device-ip>:4600/`

### Security Notes

- Do not commit real `rid_config.json`
- Keep webhook keys and local-only settings out of Git
- Commit `rid_config.example.json` only
