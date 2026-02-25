# Light RID Scanner

OpenDroneID / Remote ID Wi-Fi scanner for DJI and other RID-capable drones, with:

- live TUI or `--no-tui` text mode
- web UI (table + map + logs + AP list)
- historical drone cache (persisted across restarts)
- WeCom (Enterprise WeChat) robot notifications
- AP vendor lookup via local IEEE OUI database (`oui.txt`, auto-download supported)

The project is currently a single-file script: `run.py`.

## 中文说明

### 功能

- 监听并解析 OpenDroneID / Remote ID Wi-Fi 广播
- 网页端实时显示：
  - 无人机表格（在线/离线、首次/最后上线）
  - 地图轨迹
  - AP 扫描日志
  - 实时 AP 列表（含厂商/类型）
- 日志面板、地图面板可折叠
- 历史缓存持久化（重启后保留）
- 企业微信机器人通知（仅上线；重新上线支持冷却时间）
- 支持网页端高级选项（重启程序、指定参数、可保存）

### 环境要求

- Linux（推荐树莓派 / Ubuntu）
- Python 3.10+（已在树莓派 Python 3.13 验证）
- 无线网卡支持监听模式（monitor mode）
- `iw` / `iwconfig` 等系统工具可用
- root 权限抓包（建议 `sudo` 运行）

### Python 依赖

核心依赖为 `scapy`：

```bash
pip install scapy
```

### 关键文件

- `run.py`: 主程序
- `rid_models.json`: DJI 机型前缀映射（示例已提供）
- `rid_config.example.json`: 配置模板（公开安全版本，无 webhook key）
- `rid_config.json`: 你本地实际配置（默认被 `.gitignore` 忽略）

建议先复制模板：

```bash
cp rid_config.example.json rid_config.json
```

然后修改 `rid_config.json` 中的企业微信 webhook key 等配置。

### 启动示例

固定信道（默认常用 `ch6`）：

```bash
sudo python3 run.py --no-tui
```

指定信道：

```bash
sudo python3 run.py --no-tui --channel 6
```

跳频：

```bash
sudo python3 run.py --no-tui --hop
```

发送企业微信测试通知（不抓包）：

```bash
python3 run.py --notify-test --no-tui
```

### 网页端

默认地址：

- `http://<设备IP>:4600/`

网页端支持：

- SN 复制按钮
- DJI 信息查询按钮（新标签页/新窗口打开）
- 清空历史缓存
- 高级选项：
  - 仅本次重启
  - 保存参数并重启

### OUI 厂商库说明

- 程序会优先读取本地 `oui.txt`
- 如果不存在且配置允许，会自动下载 IEEE OUI 数据库
- 下载失败时 AP 厂商会显示“未知”（不会一直卡在“加载中”）

### 树莓派 `screen` 运行示例

```bash
screen -S RID-Receiver
cd ~/rid
sudo ~/rid/.venv/bin/python3 run.py --no-tui
```

重新连接：

```bash
screen -x RID-Receiver
```

### 安全提示

- 不要把真实 `rid_config.json`（尤其是企业微信 webhook key）直接公开到 GitHub
- 仓库中建议提交 `rid_config.example.json` 作为模板

## English

### Features

- Sniffs and decodes OpenDroneID / Remote ID Wi-Fi broadcasts
- Web UI with:
  - live drone table (online/offline, first/last seen)
  - map and trails
  - AP scan log
  - realtime AP list with vendor/type
- Collapsible log panel and map panel
- Persistent history cache across restarts
- WeCom (Enterprise WeChat) bot notifications (online-only, re-online cooldown)
- Web advanced controls (restart with args, optionally save args)

### Requirements

- Linux (Raspberry Pi recommended)
- Python 3.10+
- Wi-Fi adapter supporting monitor mode
- `iw` tools available
- root privileges for sniffing (`sudo`)

### Python dependency

```bash
pip install scapy
```

### Files

- `run.py`: main program
- `rid_models.json`: DJI model prefix map
- `rid_config.example.json`: safe public config template (no webhook key)
- `rid_config.json`: your local runtime config (ignored by default)

Create your local config:

```bash
cp rid_config.example.json rid_config.json
```

Then fill your own WeCom webhook key and other settings.

### Run examples

```bash
sudo python3 run.py --no-tui
sudo python3 run.py --no-tui --channel 6
sudo python3 run.py --no-tui --hop
python3 run.py --notify-test --no-tui
```

### Web UI

Default URL:

- `http://<device-ip>:4600/`

Includes:

- SN copy button
- DJI lookup button
- clear history button
- advanced restart controls

### OUI vendor database

- Reads local `oui.txt` first
- Auto-downloads IEEE OUI DB if enabled and missing
- Falls back to `Unknown` if unavailable (no endless “loading” state)

### Security note

Keep your real `rid_config.json` private. Commit `rid_config.example.json` instead.
