# Light RID Scanner

[English](README.md) | [简体中文](README.zh-CN.md)

## 节点中心 Viewer

`viewer/server.py` 是独立 node-center 服务，用于聚合多个 `station_edition` 子站。

```bash
python viewer/server.py --host 0.0.0.0 --port 4700
```

打开：

- `http://<中心节点IP>:4700/`

Viewer 使用 `viewer/cfg.db` 保存自身配置：节点 API 地址、节点 API Token，以及可选的 Viewer 密码登录 / SSO check 登录设置。远端飞机、基站、AP、轨迹和健康状态不会落库；每次刷新都会从各子站 API 实时读取并聚合显示。

Viewer 的实时/历史主界面直接复用 `station_edition/light_rid/web_server.py` 的 Station 页面模板；viewer 代码只替换数据/API 层，并从 DOM 中删除 Station 专用控制项。`/settings` 复用 Station 设置页风格，只保留 Viewer 主机状态、地图默认位置/缩放、密码登录、SSO check 登录和许可协议。节点管理单独放在 `/nodes`，支持节点卡片、负载曲线、扫描统计、一键生成子站 SSO 登录 URL，以及多节点批量重启程序 / 更新识别库。

Viewer 二进制由单独的 `.github/workflows/build-viewer.yml` 构建，覆盖 Linux `x86_64`、Linux `x32`、Linux `arm64`、Windows `windows-x86_64` 和 Windows `windows-x32`。本地构建命令：

```bash
python pytools/build_viewer.py --target x86_64
```

Light RID Scanner 是一个面向树莓派和其他 Linux 采集节点的固定式 Remote ID / OpenDroneID Wi-Fi 监测器。


## 版本目录

- `station_edition/`
  完整基站版本，包含扫描、网页、安全鉴权、systemd/AP 维护和树莓派部署默认逻辑。
- `portable_edition/`
  WIP（Work in Progress，开发中）。移动版运行时代码已按新策略清空，当前目录只保留 WIP 说明。
- 根目录 `run.py`
  基站版本兼容入口，实际跳转到 `station_edition/run.py`。
- 根目录 `rid-models.json`
  面向 GitHub Raw 的公开机型库；二进制内也会嵌入同一份资源，运行目录缺失时可自动恢复。

基站版优先从自身目录运行。未显式传入路径时，`config.json`、`history-cache.json` 和 `rid-models.json` 等运行文件都按当前工作目录解析。

## 功能概览

- 现代化局域网页面
- 独立 `/settings` 设置页，支持可视化编辑
- 独立 `/hardware-assistant` 硬件助手页面
- 服务端通知中心，多浏览器会话同步
- 飞机历史与轨迹持久化
- 从 RID `System` 消息中提取飞手位置
- Wi-Fi AP 扫描，支持 MAC OUI 厂商识别

### 网页仪表盘
- 基于 Leaflet 的实时地图，展示飞机标记、基站位置和报警区域
- 飞机列表面板，包含实时详情卡片（序列号、型号、高度、速度、航向、RSSI）
- AP 列表面板，显示厂商识别结果
- 深色/浅色主题切换
- 响应式网格布局，适配不同屏幕尺寸
- 地图自动居中，支持可配置的空闲超时

### 数据持久化
- 飞机历史记录，包含首次/最后发现时间戳
- 每架飞机的 GPS 轨迹存储
- 服务端缓存（`rid_history_cache.json`），服务重启后继续保留
- 可配置的飞机离线判定时间（默认 15 秒）

### 设置页 (`/settings`)
- 所有运行时配置的可视化编辑
- 基站位置管理（手动输入或浏览器定位）
- 多个企业微信 Webhook 通道管理
- 多个矩形报警区域配置
- 通行密钥注册与删除，支持无密码浏览器登录
- 受管理的 SSO 登录链接生成（需再次验证密码）
- 原始配置树浏览器 — 在配置根目录内查看、编辑、保存、删除文件（需二次密码解锁）
- 一键运行时安全修复 — 创建 `rid` 服务用户、授予采集/热点能力
- `iw` 无线工具安装助手
- systemd 服务注册与更新
- 按 Git 提交号手动检查应用新版本
- 在线识别库更新，支持可配置地址与手动触发
- 可选远程配置更新，从可配置地址拉取
- 主机负载趋势卡片（CPU、内存、温度、系统负载、AP 数），支持 12h / 24h / 7d 窗口
- 可配置的指标保留时间（默认 7 天）

### 硬件助手 (`/hardware-assistant`)
- 列出所有无线网卡及其状态
- 查看 `iw dev`、`iw info`、`iw link` 输出
- 在监控模式与托管模式之间切换网卡
- 设置指定网卡的信道
- 重启单个网卡
- 重启主扫描进程

### 通知
- 服务端通知中心，所有浏览器会话同步
- 飞机上线/离线事件
- 报警区域进入事件
- 识别库更新结果（成功/失败）
- 内置页面提交的手动通知
- 单条删除或一键清空

### 企业微信
- 多 Webhook 通道支持
- 每个通道独立启用/禁用
- 上线通知发送至所有已启用通道
- 测试通知发送至所有已启用通道
- 可配置的发送超时与重复上线冷却时间
- 向下兼容旧版单 Key 字段

### 安全
- 基于密码的浏览器登录，凭据使用 scrypt 哈希存储
- 通行密钥（WebAuthn）支持，从初始密码登录引导注册
- SSO 登录链接，基于服务端 check 校验码
- 可配置的会话有效期（默认 30 分钟）
- 外部 API 的 IP 白名单
- 登录、SSO 创建、Token 显示、API Token 失败均触发内存限流
- 敏感字段（Webhook Key、API Token）在可视化界面中遮罩显示

---

## 快速开始

### 环境要求

- **Linux**（推荐 Raspberry Pi OS；`arm64` 产物需 64 位系统）
- 支持**监控模式**的无线网卡
- 切换监控模式/信道需要 **root 权限**
- 使用 AP 热点模式时需要 `iw` 和 `hostapd`
- Python 3.10+

### 源码运行（基站版）

```bash
cd station_edition
python3 -m venv .venv
source .venv/bin/activate
pip install -r ../requirements.txt
python run.py --no-tui
```

移动版当前为 WIP，没有可运行的源码入口。

移动版自动禁用鉴权、通知和主机监控功能。

### 二进制部署

CI 产出单文件编译二进制，适用于 Linux。首次启动只需放置二进制文件，缺失的配置和历史文件会自动创建。

```bash
install -m 0755 light_rid_station-arm64 /opt/light-rid/light_rid_station-arm64
```

配置 systemd 直接执行：

```ini
[Unit]
Description=Light RID Scanner
After=network.target

[Service]
ExecStart=/opt/light-rid/light_rid_station-arm64 --config /opt/light-rid/config.json --no-tui
```

默认网页地址：

- `http://<设备IP>:4600/`

## 固定网卡绑定与 OOBE

- 扫描器不再自动递增轮换网卡。
- `basic.iface` 现在被视为固定绑定项；如果这张网卡不存在，服务会保持降级运行并提示配置，而不是悄悄切到别的网卡。
- `basic.lost_timeout` 用于配置飞机离线判定时间，默认 15 秒。
- OOBE 和设置页提供“自定义网卡绑定”，可以把每张网卡设置为 `scan`（扫描）、`web`（网页服务）、`ap_web`（AP 热点网页服务）、`disabled`（禁用）、`idle`（闲置）或 `none`；`scan` 会同步写回 `basic.iface`。
- `ap_web` 会通过 `hostapd` 配置热点，使用内置 DHCP 在 `172.16.0.0/24` 分配地址，并在服务具备所需 Linux capability 时把网页服务暴露到 `172.16.0.1:80`。
- 如果 `config.json` 缺失、损坏，或者还没有绑定默认网卡，网页会进入 `/oobe` 初始化流程。
- OOBE 用来完成最小可运行配置：
  - 选择默认无线网卡
  - 设置 RID 信道
  - 可选填写基站坐标
  - 可选设置网页登录账号和密码
这样做的目的很直接：多网卡环境下不再抓错卡，启动异常也会直接暴露为配置问题，方便固定基站长期稳定运行。

## 主要页面

- `/`
  主页面，包含地图、飞机列表、AP/日志视图切换。
- `/settings`
  可视化设置、账号密码 / 通行密钥登录控制、原始配置编辑、运行时安全修复、配置 / 版本更新工具、通知设置、报警区域设置、API 说明。
- `/hardware-assistant`
  网卡状态、`iw` 检查、监控/托管模式切换、信道调整、网卡重启、主程序重启。

## 关键文件

- `run.py`
  基站版本兼容入口。
- `station_edition/run.py`
  基站版本源码和构建入口。
- `station_edition/light_rid/`
  拆分后的扫描、解析、HTTP/WS 服务、内嵌页面、API、设置、认证、硬件辅助和 CLI/TUI 模块。
- `portable_edition/README.md`
  移动版 WIP 说明。
- `rid-models.json`
  GitHub Raw 机型前缀映射表，也是二进制内置资源的源文件。
- `station_edition/config.example.json`
  可提交到 Git 的安全示例配置。
- `config.json`
  实际运行配置，不应提交。
- `EULA.md`
  内置 EULA 同意页面显示的源文本。
- `history-cache.json`
  运行时生成的历史 / 轨迹缓存。
- `config.json.rollback`
  配置文件回滚副本。
- `rid_build_info.json`
  本地构建版本标记，用于页面版本号，例如 `commit:ba15d57#3`。
- 临时目录 `light_rid_scanner/host_metrics.jsonl`
  运行期主机负载趋势数据。不存在会自动创建，不应提交。

## 配置结构

运行配置分为以下几个主分区：

- `basic`
  采集与运行参数。
- `notify`
  企业微信通知通道与通知节奏。
- `web`
  地图、基站、报警区域和 UI 标签配置。
- `ap`
  AP 列表上限与厂商数据库配置。
- `auth`
  浏览器网页登录 / 会话鉴权、通行密钥和 SSO 链接。
- `api`
  外部 API 的 Token 鉴权。
- `model_update`
  在线识别库更新设置。
- `config_update`
  可选的远程配置更新设置。
- `app_update`
  用于手动版本比对的上游提交检查设置。
- `metrics`
  主机负载趋势保留时间设置。

示例配置文件：

- `station_edition/config.example.json`

## Token API 重点说明

### Token 保护哪些接口

当启用 Token 鉴权后，以下路径会被保护：

- `GET /api/docs`
- `GET /api/health`
- 所有 `/api/v1/*`

典型接口包括：

- `GET /api/v1/snapshot`
- `GET /api/v1/drones`
- `GET /api/v1/drones/{sn}`
- `GET /api/v1/tracks/{sn}`
- `GET /api/v1/aps`
- `GET /api/v1/logs?type=event|scan|ap&limit=200`
- `POST /api/v1/history/clear`
- `POST /api/v1/history/delete`
- `POST /api/v1/tracks/clear`
- `POST /api/v1/config/reload`

### Token 怎么传

支持两种请求头写法：

1. `X-API-Token`
2. `Authorization: Bearer <token>`

示例：

```bash
cp station_edition/config.example.json config.json
```

然后根据你的硬件和部署需求编辑 `config.json`。

### 运行时文件解析规则

运行时文件相对于当前工作目录解析，除非通过命令行参数显式指定路径：

| 文件 | 用途 | 自动创建？ |
|---|---|---|
| `config.json` | 主运行时配置 | 是（基于默认值） |
| `rid_history_cache.json` | 飞机历史与轨迹缓存 | 是（空文件） |
| `rid_models.json` | RID 机型前缀到名称的映射 | 是（从 GitHub 或内嵌资源） |
| `oui.txt` | MAC OUI 厂商数据库 | 可选（自动下载） |
| `light_rid_scanner/host_metrics.jsonl` | 主机负载采样数据 | 是（系统临时目录） |

`--config` 参数可指向任意路径：

```bash
python run.py --config /etc/light-rid/config.json --no-tui
```

---

## 网页界面

### 主页 (`/`)

首页为全屏仪表盘布局，包含四个区域：

1. **顶部栏** — 实时统计（飞机数量、AP 数量、运行时长），扫描状态指示器，主题切换
2. **地图面板** — 基于 Leaflet 的地图，显示飞机标记（带航向箭头）、基站图标和已启用的报警区域矩形框。飞机标记通过 WebSocket 推送实时更新。点击标记弹出详情卡片，包含序列号、型号、高度、速度、航向、RSSI 和最后发现时间。
3. **底部面板** — 可在飞机列表、AP 列表和事件日志视图之间切换。飞机列表按最后发现时间排序显示紧凑卡片。AP 列表显示检测到的 Wi-Fi 接入点及 OUI 数据库厂商名称。
4. **底部导航** — 跳转至 `/settings`、`/logs`、`/hardware-assistant` 的链接及主题切换。

### 设置页 (`/settings`)

设置页以可折叠卡片形式组织可视化编辑器：

- **基本设置** — 网卡、信道、跳频行为、驻留时间、离线判定、调试开关
- **通知设置** — 企业微信通道列表，支持添加/编辑/删除/测试每个通道
- **Web 设置** — 基站名称、坐标（支持浏览器定位填充）、默认缩放、DJI 查询链接
- **报警区域** — 多个矩形区域，每个区域可独立启用/禁用
- **AP 设置** — 列表上限、厂商数据库配置
- **鉴权设置** — 启用/禁用网页登录、会话有效期、登录方式（密码/通行密钥）
- **通行密钥** — 注册新密钥、删除已有密钥
- **SSO 链接** — 生成受管理的登录链接（需密码再次验证），删除可立即使其失效
- **API 设置** — 外部 API 启用/禁用、带过期时间和单次使用选项的多 Token 管理
- **识别库更新** — 更新地址、启用/禁用自动检查、手动更新按钮
- **配置更新** — 远程配置地址、启用/禁用、手动拉取按钮
- **版本更新** — 与上游 Git 仓库的提交比对
- **主机监控** — 启用/禁用主机指标采集、保留时间、趋势图表
- **原始配置** — 密码再次验证后的配置树浏览器，支持行内编辑/保存/删除
- **安全修复** — 一键创建服务用户、授权能力、安装 `iw`、注册 systemd 服务
- **导入导出** — 独立的配置文件导入导出和扫描数据导入导出

### 硬件助手 (`/hardware-assistant`)

专用于无线网卡操作的页面：

- 列出所有检测到的无线网卡及当前模式、信道和状态
- 显示原始 `iw dev`、`iw info`、`iw link` 输出供排查
- 提供按钮将每个网卡在监控模式与托管模式之间切换
- 信道设置器，支持选择目标网卡
- 网卡重启按钮
- 扫描器进程重启按钮

### 日志页 (`/logs`)

以选项卡界面提供多种日志视图：

- **运行日志** — 主扫描器日志输出
- **操作日志** — 配置变更、鉴权事件、更新操作的审计记录
- **扫描日志** — 原始 Wi-Fi 采集日志
- **差异视图** — 运行日志与扫描日志的 unified diff
- **导出** — 单项文本导出或全部 ZIP 导出
- **API 文档** — `GET /api/docs` 的渲染视图

敏感字段（Webhook Key、API Token）在可视化显示中遮罩处理。保持遮罩字段不变即可沿用已存储的值。

---

## 网卡绑定与 OOBE

### 固定网卡绑定

`basic.iface` 被视为固定绑定项。扫描器不会在可用网卡之间自动轮换。如果指定的网卡在启动时缺失，服务会保持降级运行，并通过网页界面提示配置异常，而不是悄悄切换到其他网卡。

这种设计确保了多网卡环境下的可预测性——扫描器始终使用预期网卡，启动异常会直接暴露为配置问题。

### 开箱初始化流程 (OOBE)

当 `config.json` 缺失、损坏或无绑定网卡时，网页界面会自动进入 OOBE 流程（`/oobe`）。该引导式设置收集完成最小可用配置所需的信息：

1. **选择无线网卡** — 从检测到的网卡中选择
2. **设置 RID 信道** — 选择监听信道
3. **基站坐标**（可选）— 设置地图中心点
4. **网页登录凭据**（可选）— 设置浏览器鉴权的用户名和密码

OOBE 完成后，配置写入磁盘并加载正常仪表盘。

### AP 热点模式

通过自定义网卡绑定设置，可为网卡分配 `ap_web` 角色。配置后：

- `hostapd` 使用指定 SSID 和密码创建 Wi-Fi 热点
- 内置 DHCP 服务器在 `172.16.0.0/24` 范围分配地址
- 网页界面暴露于 `172.16.0.1:80`
- 热点运行于可配置的信道（默认：6）

这允许扫描器通过自己的 Wi-Fi 网络提供网页服务，适用于没有现成网络基础设施的现场部署。

每张检测到的网卡可分配以下角色之一：`scan`（扫描）、`web`（网页服务）、`ap_web`（AP 热点）、`disabled`（禁用）、`idle`（闲置）或 `none`。`scan` 角色会同步回 `basic.iface`。

---

## 鉴权系统

### 网页登录鉴权

浏览器鉴权使用标准的 `/login` 页面与会话 Cookie，而非 HTTP Basic Auth 弹窗。配置示例：

```json
{
  "auth": {
    "enabled": true,
    "username_hash": "<scrypt(username)>",
    "password_hash": "<scrypt(password)>",
    "session_ttl_min": 30,
    "realm": "Light RID Scanner",
    "login_methods": ["password", "passkey"]
  }
}
```

生成和程序一致的 scrypt 哈希：

```bash
python3 - <<'PY'
import base64, hashlib, secrets

def hash_secret(text):
    salt = secrets.token_bytes(16)
    digest = hashlib.scrypt(
        text.encode(), salt=salt,
        n=2**14, r=8, p=1, dklen=32
    )
    return "scrypt$16384$8$1$%s$%s" % (
        base64.urlsafe_b64encode(salt).decode().rstrip("="),
        base64.urlsafe_b64encode(digest).decode().rstrip("="),
    )

print("user:", hash_secret("your_username"))
print("pass:", hash_secret("your_password"))
PY
```

如果你只保留 `api.token_hash`，外部 API 仍然可用，但设置页面将无法显示或复制当前 Token，因为系统只拿到了哈希。

### 推荐使用方式

建议这样做：

- 在本地生成一个随机 Token
- 如果希望后续能在设置页里再次显示/复制 Token，就让 `api.token` 和 `api.token_hash` 一起保存并保持一致
- 如果调用端 IP 范围固定，建议打开白名单模式
- 明文 Token 只保留在脚本、客户端、密码管理器或密钥管理系统里
- 不要把真实 Token 提交到 Git

### 一个重要行为

如果 `api.enabled = false`，那么 `/api/docs`、`/api/health` 和 `/api/v1/*` 不再默认对局域网开放，而是只允许当前内置页面通过会话方式调用。

这意味着：

- 外部脚本必须等你显式开启外部 API 后才能访问
- Light RID Scanner 自带页面仍可正常工作
- 网页登录会话不会直接放行 Token API 路径

## 网页登录鉴权 与 Token API 鉴权的区别

这两套机制是分开的。

### 网页登录鉴权

它用于浏览器页面和基于当前会话的辅助接口。浏览器现在使用 `/login` 登录页和会话 Cookie，不再弹出 HTTP Basic 登录框。

配置示例：

```json
{
  "auth": {
    "enabled": true,
    "username_hash": "<scrypt(username)>",
    "password_hash": "<scrypt(password)>",
    "session_ttl_min": 30,
    "realm": "Light RID Scanner"
  }
}
```

生成和程序一致的用户名 / 密码 scrypt 哈希：

```bash
python3 - <<'PY'
import base64, hashlib, secrets
def hash_secret(text):
    salt = secrets.token_bytes(16)
    digest = hashlib.scrypt(text.encode(), salt=salt, n=2**14, r=8, p=1, dklen=32)
    return "scrypt$16384$8$1$%s$%s" % (
        base64.urlsafe_b64encode(salt).decode().rstrip("="),
        base64.urlsafe_b64encode(digest).decode().rstrip("="),
    )
print("user:", hash_secret("your_user"))
print("pass:", hash_secret("your_pass"))
PY
```

受信任的外部启动器可以使用 SSO 形式登录。URL 只使用服务端保存的 `check` 校验码：

```text
/login?check=<server-check-code>
```

设置页负责生成和保存 `check` 校验码。从设置页列表中删除该项后，对应链接立即失效。

旧快捷方式如果仍带有 `user` 或 `password` 参数，这些值会被当作普通字符串忽略；真正校验的只有 `check`：

```text
/login?user=<ignored>&password=<ignored>&check=<server-check-code>
/login?user=<ignored>?password=<ignored>?check=<server-check-code>
```

设置页会在再次验证账号和密码后生成 SSO 登录链接。该链接可直接加入外部 SSO 启动器，并一直有效，直到对应 `check` 被删除。

网页登录会话过期后，内置页面再次请求接口会收到鉴权失败，并自动回到 `/login`。

### 只给网页会话用的辅助接口

这些接口主要给内置页面使用，依赖当前浏览器会话：

- `GET /api/notifications?limit=200`
- `POST /api/notifications` / `POST /api/notifications/delete` / `POST /api/notifications/clear`

**设置类**
- `GET /api/settings/view` / `GET /api/settings/runtime`
- `GET /api/settings/metrics?window=12h|24h|7d`
- `GET /api/settings/systemd/status`
- `GET /api/settings/api-docs`
- `GET /api/logs/view?type=runtime|operation|scan|scan_diff|ap`
- `GET /api/logs/export?type=all|runtime|operation|scan|scan_diff|ap`
- `POST /api/settings/visual/test`
- `POST /api/settings/visual/save`
- `POST /api/settings/raw/unlock`
- `POST /api/settings/raw/save`
- `GET /api/config/file?path=<配置根目录内路径>`
- `POST /api/config/file/delete`
- `POST /api/settings/notify/test`
- `POST /api/settings/passkey/start`
- `POST /api/settings/passkey/finish`
- `POST /api/settings/passkey/delete`
- `POST /api/passkey/login/start`
- `POST /api/passkey/login/finish`
- `GET /api/settings/models/list`
- `POST /api/settings/models/save`
- `POST /api/settings/models/upsert`
- `POST /api/settings/models/update`
- `POST /api/settings/app-update/check`
- `POST /api/settings/systemd/register`
- `POST /api/settings/iw/install`
- `POST /api/settings/security/repair`
- `POST /api/settings/login-link/create`
- `POST /api/settings/login-link/delete`
- `GET /api/hw/status`
- `POST /api/hw/op`
- `GET /api/config`
- `GET /api/tools/export/all`
- `GET /api/tools/export/track?sn=<SN>`
- `GET /api/tools/diagnostic.zip`
- `POST /api/tools/import/all` / `POST /api/tools/import/track`
- `GET /api/tracks/get?sn=<SN>` / `POST /api/tracks/clear`
- `POST /api/history/delete` / `POST /api/history/clear`

它们和 `/api/v1/*` 不是一套鉴权逻辑。

### 设置页里的 Token 显示/复制

- API Token 支持多个条目，每个条目可设置有效期、单次使用或无限时间
- 已保存的 API Token 默认遮罩显示，显示或复制前必须再次输入网页登录账号和密码
- 这次再次验证沿用网页登录凭据；外部 API 开启后仍必须使用有效 API Token
- 生成 SSO 登录链接也需要同样的再次验证
- 登录、SSO 登录链接、Token 显示/复制、外部 API Token 失败都会触发内存限流，并写入操作日志。

## API 总览

### 发现接口

- `GET /api/docs`
  返回 API 元数据、鉴权说明和接口索引。
- `GET /api/health`
  简单健康检查。

### 读取类接口

- `GET /api/v1/snapshot`
  获取完整运行时快照。
- `GET /api/v1/auth/status`
  获取鉴权状态摘要。
- `GET /api/v1/drones`
  获取飞机列表。
- `GET /api/v1/drones/{sn}`
  获取单架飞机详情。
- `GET /api/v1/tracks/{sn}`
  获取单架飞机轨迹。
- `GET /api/v1/aps`
  获取实时 AP 列表。
- `GET /api/v1/logs?type=event|scan|ap&limit=200`
  获取事件 / 扫描 / AP 日志。

### 写入类接口

- `POST /api/v1/history/clear`
  清空全部历史。
- `POST /api/v1/history/delete`
  删除单架飞机历史记录。
- `POST /api/v1/tracks/clear`
  清空所有轨迹，或按请求体清空指定轨迹。
- `POST /api/v1/config/reload`
  从磁盘重新加载配置。

## 设置页

打开方式：

- `/settings`

支持内容：

- 可视化编辑运行 / 采集参数
- 可视化编辑多个企业微信通道
- 可视化编辑多个报警区域
- 编辑基站位置
- 通过浏览器定位填充基站坐标
- 在线更新 RID 识别库，支持修改更新地址并手动触发
- 支持从可配置地址在线更新完整运行配置
- 可选开启主机负载趋势，按 CPU、内存、温度、系统负载、AP 数拆分展示
- 主机负载趋势支持 12 小时、24 小时、7 天视图
- 主机负载数据保留时间可配置，默认 7 天
- 再次验证账密后生成和删除可管理的 SSO 登录链接
- 支持通行密钥的添加和删除，用于网页登录
- 再次验证密码后浏览 / 编辑 / 保存 / 删除原始配置树
- 支持运行时安全修复、`iw` 安装和 systemd 服务注册 / 更新
- 支持按上游 Git 提交号手动检查程序新版本

### 在线识别库更新

设置页可以从远端 JSON 文件更新 `rid-models.json`。默认地址：

```text
https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/refs/heads/main/rid-models.json
```

行为说明：

- 启用后每天自动检查一次
- 手动更新按钮使用同一个地址
- 地址必须以 `http://` 或 `https://` 开头
- 更新成功或失败都会写入操作日志和通知中心
- 同一个设置卡片可以把 `rid-models.json` 作为前缀/机型列表编辑
- 机型为 N/A 的详情卡片可以直接写入本地识别库，或打开预填的 GitHub Issue / PR 编辑页

### 远程配置更新

设置页可以按需从远端 JSON 文件拉取完整运行配置。

行为说明：

- 地址必须以 `http://` 或 `https://` 开头
- 下载到的 JSON 仍必须能通过完整配置校验
- 更新流程会先合并默认值，再备份、写入并重载
- 如果重载失败，会立刻恢复保存前的备份
- 成功和失败都会写入操作日志

### 通行密钥、原始配置与运行时修复

- 通行密钥以现有网页登录账号密码为引导完成首次注册，之后保存在 `auth.passkeys`。
- 原始配置编辑被限制在当前配置根目录内，并且需要当前浏览器会话先完成一次短时二次解锁。
- 运行时修复卡片可以创建 / 确认 `rid` 专用运行账号、授予采集和热点能力、安装无线工具，并注册 / 更新 `light-rid-scanner.service`。
- 二进制部署时，systemd 服务应始终指向已安装的基站二进制文件、当前配置文件路径以及 `--no-tui` 服务运行模式。

### 主机负载趋势

设置页将主机负载拆成多个独立小图：

- CPU
- 内存
- 温度
- 系统负载
- AP 数

节点负载默认关闭。开启后数据约每分钟采样一次，默认写入系统临时目录下的 `light_rid_scanner/host_metrics.jsonl`。文件不存在会自动创建，服务重启后继续沿用，并按 `metrics.retention_days` 自动裁剪。

### 构建版本

页面版本号格式为：

```text
commit:<Git短提交号>#<本地构建号>
```

`rid_build_info.json` 保存当前 Git 短提交号和本地构建号。CI 工作流会生成基站版 Linux 单文件产物，覆盖 `x86_64`、`x32`、`arm64` 和 `armv7`；移动版产物在 WIP 阶段暂停。

本地构建可以使用根目录共享入口，也可以进入版本目录使用本地包装脚本：

```bash
python pytools/build_release.py --edition station --target arm64
cd station_edition
python pytools/build.py --target arm64
```

`x32` 目标必须使用 32 位 Python 运行时构建；GitHub Actions 工作流会通过单独的 Linux 32 位 Docker job 完成。

设置页可以手动比较本地程序提交号和远端 Git 提交号。这个检查只报告是否存在更新，不会自动下载、套用代码或重启服务。

当前工作区准备发布的版本线是 `v2.0`，但页面仍继续使用上面的 commit 构建标记，便于定位每一次本地构建。

## 通知中心

通知中心基于服务端内存存储，通过 `/api/notifications` 同步到所有活跃浏览器会话。与浏览器本地存储不同，通知可在页面刷新后继续存在，且任意已连接的浏览器均可查看。

**通知来源：**
- 飞机上线/离线事件
- 报警区域进入事件
- 识别库更新结果（成功/失败）
- 内置页面提交的手动通知

通知可单条删除或在页面上批量清空。

---

## 企业微信通知

系统支持多个企业微信 Webhook 通道用于飞机上线提醒：

```json
{
  "notify": {
    "enabled": true,
    "send_timeout_sec": 8,
    "notify_reonline": true,
    "reonline_cooldown_sec": 300,
    "wecom_webhooks": [
      {
        "name": "主通道",
        "enabled": true,
        "key": "YOUR_WEBHOOK_KEY"
      },
      {
        "name": "备用通道",
        "enabled": false,
        "key": "YOUR_BACKUP_KEY"
      }
    ]
  }
}
```

**行为说明：**
- 上线通知会发送至所有已启用通道
- 测试通知（从设置页发送）会发送至所有已启用通道
- 重复上线通知受 `reonline_cooldown_sec`（默认：300 秒）限流
- 旧版 `notify.wecom_webhook_key` 单 Key 字段仍兼容
- Webhook Key 在设置界面中遮罩显示

---

## 报警区域

可定义多个矩形报警区域，在地图上以红色矩形框显示：

```json
{
  "web": {
    "alarm_zones": [
      {
        "name": "北侧区域",
        "enabled": true,
        "lat1": 30.000000,
        "lon1": 121.000000,
        "lat2": 30.010000,
        "lon2": 121.010000
      }
    ]
  }
}
```

**行为说明：**
- 已启用的区域在地图上以红色矩形框渲染
- 无人机进入已启用区域时触发全屏浏览器警告
- 若用户已授权浏览器通知，会同时弹出系统通知
- 旧版 `web.alarm_zone` 单区域字段仍兼容

---

## 主机负载监控

启用后，扫描器约每分钟采样一次主机指标，存储在系统临时目录的 `light_rid_scanner/host_metrics.jsonl` 中。文件自动创建，服务重启后继续沿用，按 `metrics.retention_days`（默认 7 天）自动裁剪。

**监控指标：**
- CPU 使用率
- 内存使用率
- 温度（自动检测传感器或手动指定来源）
- 系统负载
- AP 数量

设置页将这些指标拆分为独立的小型趋势图，可选择 12 小时、24 小时或 7 天时间窗口。

```json
{
  "metrics": {
    "enabled": true,
    "retention_days": 7,
    "temperature_source": "auto"
  }
}
```

主机监控默认关闭。在 `/settings` 中开启后开始采集。

---

## 识别库在线更新

RID 识别库（`rid_models.json`）将 RID 前缀码映射为可读的无人机型号名称，可通过可配置的 URL 在线更新。

**默认更新源：**
```
https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/refs/heads/main/rid_models.json
```

**行为说明：**
- `model_update.enabled` 为 `true` 时每天自动检查一次
- 手动更新使用设置页中同一地址
- 地址必须以 `http://` 或 `https://` 开头
- 更新成功或失败均写入操作日志和通知中心
- 设置页同时也支持以前缀/机型表格形式直接编辑识别库
- 型号显示为 "N/A" 的飞机详情卡片提供添加本地映射或打开预填的 GitHub Issue/PR 编辑页选项

二进制构建中内嵌了 `rid_models.json` 的快照作为回退资源。若运行时文件缺失且网络不可用，自动恢复内嵌副本。

---

## 导入与导出

系统为设置和扫描数据提供独立的导出导入流程：

**设置（配置）：**
- `GET /api/settings/export/settings` — 导出当前配置 JSON
- `POST /api/settings/import/settings` — 导入并合并设置

**扫描数据（历史 + 轨迹）：**
- `GET /api/settings/export/scan-data` — 导出飞机历史与轨迹
- `POST /api/settings/import/scan-data` — 导入扫描数据

**组合工具：**
- `GET /api/tools/export/all` — ZIP 导出所有数据
- `GET /api/tools/export/track?sn=<SN>` — ZIP 导出单架飞机轨迹
- `POST /api/tools/import/all` — 从 ZIP 导入所有数据
- `POST /api/tools/import/track` — 导入轨迹数据

这些辅助功能可从设置页访问，也可由内置页面直接调用 API。

---

## 节点中心 Viewer

`viewer/server.py` 是一个独立的 Web 服务，将多个 `station_edition` 基站实例聚合为统一仪表盘。适用于管理多台固定基站的运营者，提供一站式全局视图。

### 运行 Viewer

```bash
python viewer/server.py --host 0.0.0.0 --port 4700
```

访问 `http://<中心节点IP>:4700/`。

### 数据流向

Viewer 仅在 `viewer/cfg.db` 中保存自身配置：
- 节点 API 根地址
- 节点 API Token
- 可选的 Viewer 密码登录与 SSO 登录设置

它**不会**落库存储远端飞机、基站、AP、轨迹或健康数据。每次仪表盘刷新时，Viewer 并行向各已配置基站 API 拉取当前数据并渲染聚合结果。这意味着 Viewer 对扫描数据是无状态的——停止 Viewer 后不会保留任何扫描数据。

### Viewer 页面

**`/` — 仪表盘**
- 复用 `station_edition/light_rid/web_server.py` 的 Station 页面模板
- Viewer 代码通过补丁将数据/API 层替换为从远端基站获取
- Station 专属控件（启停扫描器、信道切换等）已从 DOM 中移除

**`/settings` — Viewer 设置**
- Viewer 主机状态（运行时长、版本）
- 默认地图中心位置与缩放级别
- Viewer 自身的密码登录配置
- SSO check 登录配置
- EULA 许可协议控件

**`/nodes` — 节点管理**
- 添加、编辑、测试、删除基站节点
- 节点信息卡片，实时状态展示
- 负载图表与扫描数量统计
- 为每个节点一键生成远端 SSO 登录 URL
- 跨所选节点批量重启程序 / 更新识别库

### 添加节点

仅输入 API 根地址，例如 `http://192.168.1.10:4600`。路径、查询字符串、片段和用户信息会被拒绝——Viewer 自行拼接 `/api/v1` 路径，并在保存前通过真实 API 调用来验证连通性。

Viewer 同时通过 `X-API-Token` 和 `Authorization: Bearer <token>` 头发送已配置的 Token。

### Viewer 模块布局

| 模块 | 职责 |
|---|---|
| `viewer/server.py` | HTTP 路由、API 代理、WebSocket |
| `viewer/storage.py` | SQLite 数据库，保存配置、节点和鉴权/会话状态 |
| `viewer/aggregation.py` | 并行基站 API 拉取与数据聚合 |
| `viewer/station_ui.py` | Station HTML 模板加载与 Viewer DOM 补丁 |
| `viewer/settings_ui.py` | Viewer 专属设置页（Station 风格） |
| `viewer/nodes_ui.py` | 节点管理页（Station 风格） |
| `viewer/ui_common.py` | 从 Station 模板提取共享 CSS |
| `viewer/paths.py` | 资源路径解析 |

### 构建 Viewer

```bash
python pytools/build_viewer.py --target x86_64
```

CI 通过 `.github/workflows/build-viewer.yml` 构建 Viewer 二进制，覆盖 Linux `x86_64`、Linux `x32`、Linux `arm64`、Windows `windows-x86_64` 和 Windows `windows-x32`。

---

## 关键文件说明

| 文件 | 说明 | 可提交？ |
|---|---|---|
| `run.py` | 根目录基站版兼容入口 | 是 |
| `station_edition/run.py` | 基站版入口 | 是 |
| `station_edition/light_rid/` | 全部扫描、解析、服务、鉴权、UI 模块 | 是 |
| `portable_edition/pe.py` | 移动版入口 | 是 |
| `rid_models.json` | RID 机型前缀到型号映射 | 是 |
| `rid_build_info.json` | 本地构建标记（commit + 构建号） | 是 |
| `station_edition/config.example.json` | 安全示例配置 | 是 |
| `config.json` | 实际运行时配置 | **禁止** |
| `rid_history_cache.json` | 运行时飞机历史与轨迹 | **禁止** |
| `config.json.rollback` | 自动回滚恢复副本 | **禁止** |
| `oui.txt` | MAC OUI 厂商数据库（自动下载） | **禁止** |
| `light_rid_scanner/host_metrics.jsonl` | 主机负载采样数据（系统临时目录） | **禁止** |
| `viewer/cfg.db` | Viewer 节点与鉴权配置 | **禁止** |

UI 版本号格式为 `commit:<Git短提交号>#<构建号>`，从 `rid_build_info.json` 读取。当前发布版本线为 `v2.0`，但 UI 使用 commit 构建标签以确保本地构建的可追溯性。

---

## Git 与隐私规则

提交至 GitHub 前，确认：

- [ ] `config.json` **未**暂存
- [ ] 任何已跟踪文件中不包含真实的 Webhook Key
- [ ] 任何已跟踪文件中不包含真实的 API Token
- [ ] 未暂存运行时生成的历史或缓存文件
- [ ] 仅 `station_edition/config.example.json` 包含示例配置值

---

## OpenDroneID 参考资料

- [Open Drone ID Core C Library](https://github.com/opendroneid/opendroneid-core-c) — 官方参考实现
- [OpenDroneID Specs 仓库](https://github.com/opendroneid/specs) — 规范草案与文档

如需获取最终权威的 ASTM Remote ID 标准文本，请直接从 [ASTM International](https://www.astm.org/) 获取 ASTM F3411 正式版。
