# Light RID Scanner

[English](README.md) | [简体中文](README.zh-CN.md)

Light RID Scanner 是一个固定式 Remote ID（ASTM F3411 / OpenDroneID）Wi-Fi 监测器，专为树莓派及其他 Linux 采集节点设计。它被动监听无人机 Wi-Fi Remote ID 广播，实时解码，并通过现代化网页仪表盘展示结果。

项目还提供适用于移动部署的便携版，以及将多个基站聚合到统一视图的节点中心 Viewer。

---

## 目录

- [架构概览](#架构概览)
  - [版本目录](#版本目录)
  - [模块布局](#模块布局)
- [功能特性](#功能特性)
- [快速开始](#快速开始)
  - [源码运行（基站版）](#源码运行基站版)
  - [源码运行（移动版）](#源码运行移动版)
  - [二进制部署](#二进制部署)
  - [从源码构建](#从源码构建)
- [配置说明](#配置说明)
  - [顶级配置分区](#顶级配置分区)
  - [示例配置](#示例配置)
  - [运行时文件解析规则](#运行时文件解析规则)
- [网页界面](#网页界面)
  - [主页 (`/`)](#主页-)
  - [设置页 (`/settings`)](#设置页-settings)
  - [硬件助手 (`/hardware-assistant`)](#硬件助手-hardware-assistant)
  - [日志页 (`/logs`)](#日志页-logs)
- [网卡绑定与 OOBE](#网卡绑定与-oobe)
  - [固定网卡绑定](#固定网卡绑定)
  - [开箱初始化流程 (OOBE)](#开箱初始化流程-oobe)
  - [AP 热点模式](#ap-热点模式)
- [鉴权系统](#鉴权系统)
  - [网页登录鉴权](#网页登录鉴权)
  - [通行密钥登录](#通行密钥登录)
  - [SSO 登录链接](#sso-登录链接)
  - [会话生命周期](#会话生命周期)
- [外部 API](#外部-api)
  - [启用 API](#启用-api)
  - [发送 Token](#发送-token)
  - [生成 Token 哈希](#生成-token-哈希)
  - [API 接口参考](#api-接口参考)
  - [IP 白名单](#ip-白名单)
  - [会话辅助接口](#会话辅助接口)
- [通知中心](#通知中心)
- [企业微信通知](#企业微信通知)
- [报警区域](#报警区域)
- [主机负载监控](#主机负载监控)
- [识别库在线更新](#识别库在线更新)
- [导入与导出](#导入与导出)
- [节点中心 Viewer](#节点中心-viewer)
  - [运行 Viewer](#运行-viewer)
  - [Viewer 页面](#viewer-页面)
  - [Viewer 模块布局](#viewer-模块布局)
  - [构建 Viewer](#构建-viewer)
- [关键文件说明](#关键文件说明)
- [Git 与隐私规则](#git-与隐私规则)
- [OpenDroneID 参考资料](#opendroneid-参考资料)

---

## 架构概览

### 版本目录

仓库包含三个独立版本，分别服务于不同的部署场景：

| 目录 | 用途 |
|---|---|
| `station_edition/` | **完整基站版。** 包含扫描核心、内嵌网页 UI 的 Web 服务器、鉴权与会话管理、systemd 服务辅助、AP 热点模式，以及树莓派部署默认配置。这是固定安装场景的主要版本。 |
| `portable_edition/` | **移动便携版。** 复用扫描核心与网页核心，但启动时自动关闭网页登录、API Token、SSO 链接、通行密钥、主机负载监控和企业微信通知。适用于需要快速部署的现场作业场景。 |
| `viewer/` | **节点中心聚合器。** 独立的 Web 服务，连接多个 `station_edition` 实例，通过外部 API 获取实时数据并渲染统一仪表盘。 |

根目录 `run.py` 是一个轻量兼容入口，直接委托给 `station_edition/run.py`。每个版本均可从其自身目录独立运行。

### 模块布局

```
Light_RID_Scanner/
├── station_edition/
│   ├── run.py                       # 基站版入口
│   ├── config.example.json          # 安全示例配置（可提交）
│   └── light_rid/
│       ├── app.py                   # 应用启动与编排
│       ├── common_core.py           # 共享工具与常量
│       ├── scan_core.py             # Wi-Fi 采集、ODID 解码、DJI Beacon 解析
│       ├── process_core.py          # 飞机状态机、历史记录、轨迹管理
│       ├── hardware_core.py         # 网卡管理、iw 控制、信道操作
│       ├── auth_core.py             # 密码/通行密钥鉴权、会话管理
│       ├── network_binding_core.py  # 网卡角色分配、AP 热点配置
│       ├── web_server.py            # HTTP/WebSocket 服务器、内嵌 HTML/CSS/JS
│       ├── cli_app.py               # CLI/TUI 终端界面
│       ├── runtime.py               # 运行时上下文与模块加载器
│       └── platform_compat.py       # 平台兼容层
├── portable_edition/
│   ├── pe.py                        # 移动版入口
│   └── bootstrap.py                 # 启动覆写（关闭鉴权/通知等）
├── viewer/
│   ├── server.py                    # HTTP/API/WebSocket 路由
│   ├── storage.py                   # SQLite 配置、节点记录、鉴权状态
│   ├── aggregation.py               # 实时基站 API 拉取与聚合
│   ├── station_ui.py                # Station 模板加载与 DOM 补丁
│   ├── settings_ui.py               # Viewer 设置页
│   ├── nodes_ui.py                  # 节点管理页
│   ├── ui_common.py                 # 共享 CSS 提取
│   └── paths.py                     # 资源路径解析
├── pytools/
│   ├── build_release.py             # CI/本地发布构建器
│   └── build_viewer.py              # Viewer 二进制构建器
├── run.py                           # 根目录兼容入口
├── rid_models.json                  # RID 机型前缀映射表
├── requirements.txt                 # Python 依赖
└── .github/workflows/               # CI 构建流水线
```

基站版运行时采用模块加载架构：`app.py` 按顺序加载并执行核心模块（`common_core.py`、`scan_core.py`、`process_core.py`、`hardware_core.py`、`auth_core.py`、`network_binding_core.py`、`web_server.py`、`cli_app.py`），将它们组装到统一的命名空间中运行。这种设计简化了构建流程，同时保持源码模块相互独立、便于阅读。

---

## 功能特性

### 扫描与解码
- 被动 Wi-Fi Remote ID 采集（ASTM F3411 / OpenDroneID）
- 2.4 GHz 和 5 GHz 频段支持，可配置信道驻留时间
- 基于 RSSI 的信号检测，支持可配置的信号差值
- DJI 新固件 RID Beacon 解析（提取 UAS ID 与固件类型）
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

服务启动于 `http://<设备IP>:4600/`。首次运行没有 `config.json` 时，网页界面将自动进入 OOBE 初始化流程。

### 源码运行（移动版）

```bash
cd portable_edition
python3 -m venv .venv
source .venv/bin/activate
pip install -r ../requirements.txt
python pe.py --no-tui
```

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
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
```

二进制文件相对于工作目录解析运行时文件。若 `rid_models.json` 缺失，程序会优先尝试从 GitHub Raw 下载最新版本；网络不可用时则回退到二进制内嵌资源。

### 从源码构建

```bash
# 基站版
python pytools/build_release.py --edition station --target arm64
python pytools/build_release.py --edition station --target x86_64

# 移动版
python pytools/build_release.py --edition portable --target x86_64
python pytools/build_release.py --edition portable --target x32
```

`x32` 目标需使用 32 位 Python 运行时；GitHub Actions 工作流通过专用的 32 位 Docker Job 处理。

**CI 产物矩阵：**

| 版本 | 架构 | 运行环境 |
|---|---|---|
| station | x86_64 | ubuntu-24.04 |
| station | arm64 | ubuntu-24.04-arm |
| portable | x86_64 | ubuntu-24.04 |
| portable | arm64 | ubuntu-24.04-arm |
| portable | x32 | 32-bit Docker |

---

## 配置说明

### 顶级配置分区

运行时配置为单个 JSON 文件（`config.json`），按以下分区组织：

| 分区 | 用途 |
|---|---|
| `basic` | 采集与运行参数 — 网卡、信道、跳频设置、驻留时间、RSSI 差值、飞机超时、调试模式 |
| `notify` | 企业微信通知通道 — 每个 Webhook 的启用/禁用、发送超时、重复上线冷却 |
| `web` | 地图与 UI 配置 — 基站坐标、默认缩放、航向参考、DJI 查询链接、报警区域定义 |
| `ap` | Wi-Fi AP 扫描限制与厂商数据库设置 — AP 列表上限、OUI 文件来源 |
| `auth` | 浏览器登录与会话鉴权 — 用户名/密码哈希、会话有效期、通行密钥存储、SSO 链接列表 |
| `api` | 外部 API Token 鉴权 — 启用开关、Token 哈希、带过期时间的 Token 列表、IP 白名单 |
| `model_update` | 在线识别库更新 — 启用开关、JSON 源地址 |
| `config_update` | 远程配置更新 — 启用开关、JSON 源地址、上次检查记录 |
| `app_update` | 上游 Git 提交比对 — 启用开关、Commit API 地址 |
| `metrics` | 主机负载指标 — 启用开关、保留天数、温度传感器来源 |
| `network_bindings` | 网卡角色绑定与 AP 热点配置 — 每个网卡的角色、SSID、DHCP 范围 |

### 示例配置

完整的带注释示例配置位于 `station_edition/config.example.json`，包含所有分区的安全默认值，可直接复制并自定义：

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

生成与程序一致的 scrypt 哈希：

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

### 通行密钥登录

通行密钥（WebAuthn）在初始密码登录引导后提供无密码浏览器登录：

1. 使用用户名和密码登录
2. 在 `/settings` 中注册通行密钥 — 浏览器创建凭据对
3. 公钥存储在 `auth.passkeys` 中
4. 后续登录时，`/login` 页面提供通行密钥认证选项
5. 可随时从设置页删除通行密钥

### SSO 登录链接

对于受信任的外部启动器，SSO 式登录链接使用服务端保存的 `check` 校验码：

```
/login?check=<server-check-code>
```

设置页在再次验证用户名和密码后生成这些链接。生成的 URL 在对应 `check` 码从设置列表中删除之前始终有效。旧版携带 `user` 或 `password` 查询参数的 URL 被视为无害字符串忽略——仅 `check` 参与校验。

### 会话生命周期

- 会话有效期可通过 `auth.session_ttl_min` 配置（默认：30 分钟）
- 会话过期后，页面 API 请求返回鉴权失败
- 内置页面自动重定向至 `/login`
- 登录、SSO 创建、Token 显示、API Token 失败均触发内存限流并写入操作日志

---

## 外部 API

外部 API 为集成、脚本和节点中心 Viewer 提供机器可读的扫描器数据访问接口。

### 启用 API

需同时满足三项条件：

1. 网页登录鉴权**已启用**（`auth.enabled: true`）
2. 用户名和密码哈希**已配置**
3. API Token **已配置**（`api.token` 或 `api.token_hash`）

此设计确保外部 API 仅在操作者已显式设置鉴权时才对外暴露。

### 发送 Token

支持两种请求头格式：

```bash
# 方式一：自定义头
curl -H "X-API-Token: YOUR_TOKEN" http://0.0.0.0:4600/api/v1/snapshot

# 方式二：Bearer Token
curl -H "Authorization: Bearer YOUR_TOKEN" http://0.0.0.0:4600/api/v1/drones
```

### 生成 Token 哈希

使用与程序一致的 scrypt 格式：

```bash
python3 - <<'PY'
import base64, hashlib, secrets
salt = secrets.token_bytes(16)
digest = hashlib.scrypt(b"YOUR_TOKEN_HERE", salt=salt, n=2**14, r=8, p=1, dklen=32)
print("scrypt$16384$8$1$%s$%s" % (
    base64.urlsafe_b64encode(salt).decode().rstrip("="),
    base64.urlsafe_b64encode(digest).decode().rstrip("="),
))
PY
```

API 支持多个 Token，每个可单独设置有效期和单次使用标记。若仅存储 `api.token_hash`（不含 `api.token`），外部 API 仍可正常运作，但设置页无法显示或复制明文 Token。

**推荐使用方式：**
- 在本地生成随机 Token
- 若希望设置页后续可显示/复制 Token，同时保留 `api.token` 和 `api.token_hash`
- 调用端 IP 固定时，开启白名单模式
- 明文 Token 仅存放在 API 客户端、脚本或密钥管理系统中
- 切勿将真实 Token 提交到 Git

### API 接口参考

#### 发现接口

| 方法 | 路径 | 说明 |
|---|---|---|
| GET | `/api/docs` | API 元数据、鉴权说明与接口索引 |
| GET | `/api/health` | 简易健康检查 |

#### 读取类

| 方法 | 路径 | 说明 |
|---|---|---|
| GET | `/api/v1/snapshot` | 完整运行时快照，供集成使用 |
| GET | `/api/v1/auth/status` | 鉴权状态摘要 |
| GET | `/api/v1/drones` | 当前飞机列表 |
| GET | `/api/v1/drones/{sn}` | 单架飞机详情 |
| GET | `/api/v1/tracks/{sn}` | 单架飞机轨迹点 |
| GET | `/api/v1/aps` | 当前 AP 列表 |
| GET | `/api/v1/logs?type=event\|scan\|ap&limit=200` | 事件/扫描/AP 日志 |

#### 写入类

| 方法 | 路径 | 说明 |
|---|---|---|
| POST | `/api/v1/history/clear` | 清空全部历史 |
| POST | `/api/v1/history/delete` | 删除单架飞机的历史记录 |
| POST | `/api/v1/tracks/clear` | 清空所有轨迹或指定飞机的轨迹 |
| POST | `/api/v1/config/reload` | 从磁盘重新载入配置 |

### IP 白名单

当 `api.whitelist_enabled` 为 `true` 时，只有来自 `api.whitelist` 中地址的请求才能通过 Token 验证：

```json
{
  "api": {
    "whitelist_enabled": true,
    "whitelist": [
      "127.0.0.1",
      "192.168.1.0/24"
    ]
  }
}
```

### 会话辅助接口

以下接口供内置网页界面使用，需有效的浏览器会话（它们**不属于** Token 保护的 `/api/v1/*` 命名空间）：

**通知类**
- `GET /api/notifications?limit=200`
- `POST /api/notifications` / `POST /api/notifications/delete` / `POST /api/notifications/clear`

**设置类**
- `GET /api/settings/view` / `GET /api/settings/runtime`
- `GET /api/settings/metrics?window=12h|24h|7d`
- `GET /api/settings/systemd/status` / `GET /api/settings/api-docs`
- `POST /api/settings/visual/test` / `POST /api/settings/visual/save`
- `POST /api/settings/raw/unlock` / `POST /api/settings/raw/save`
- `POST /api/settings/notify/test`
- `POST /api/settings/passkey/start` / `POST /api/settings/passkey/finish` / `POST /api/settings/passkey/delete`
- `POST /api/settings/login-link/create` / `POST /api/settings/login-link/delete`
- `POST /api/settings/models/save` / `POST /api/settings/models/upsert` / `POST /api/settings/models/update` / `GET /api/settings/models/list`
- `POST /api/settings/app-update/check`
- `POST /api/settings/systemd/register` / `POST /api/settings/iw/install` / `POST /api/settings/security/repair`

**配置类**
- `GET /api/config` / `GET /api/config/file?path=<配置根目录内路径>`
- `POST /api/config/file/delete`

**日志类**
- `GET /api/logs/view?type=runtime|operation|scan|scan_diff|ap`
- `GET /api/logs/export?type=all|runtime|operation|scan|scan_diff|ap`

**硬件类**
- `GET /api/hw/status` / `POST /api/hw/op`

**工具类**
- `GET /api/tools/export/all` / `GET /api/tools/export/track?sn=<SN>`
- `GET /api/tools/diagnostic.zip`
- `POST /api/tools/import/all` / `POST /api/tools/import/track`
- `GET /api/tracks/get?sn=<SN>` / `POST /api/tracks/clear`
- `POST /api/history/delete` / `POST /api/history/clear`

**通行密钥登录类**
- `POST /api/passkey/login/start` / `POST /api/passkey/login/finish`

当 `api.enabled` 为 `false` 时，`/api/docs`、`/api/health` 及所有 `/api/v1/*` 路径**不对局域网开放**——仅允许内置页面通过浏览器会话方式调用。外部脚本必须等 API 被显式启用后才能访问。

---

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
