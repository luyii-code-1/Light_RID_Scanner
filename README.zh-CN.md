# Light RID Scanner

[English](README.md) | [简体中文](README.zh-CN.md)

Light RID Scanner 是一个面向树莓派和其他 Linux 采集节点的固定式 Remote ID / OpenDroneID Wi-Fi 监测器。


## 功能概览

- 现代化局域网页面
- 独立 `/settings` 设置页，支持可视化编辑
- 独立 `/hardware-assistant` 硬件助手页面
- 服务端通知中心，多浏览器会话同步
- 飞机历史与轨迹持久化
- 从 RID `System` 消息中提取飞手位置
- 支持导出全部详情和单机轨迹
- 支持 Token 保护的外部 API
- 支持网页登录 / 会话鉴权
- 支持基于通行密钥的网页登录，首次仍由账号密码引导配置
- 支持在 `/settings` 中分别导入导出设置文件与扫描数据
- 支持配置单次网页登录有效期，默认 30 分钟
- 企业微信支持多机器人通道
- 支持多个自定义报警区域并绘制到地图上
- 支持 DJI 新固件 RID Beacon 解析，并显示 UAS ID 与固件类型
- 支持在配置根目录内进行原始配置树浏览 / 编辑 / 保存 / 删除，并要求再次验证密码
- 支持一键运行时安全修复、`iw` 安装和 systemd 服务注册 / 更新
- 支持从可配置地址在线更新 RID 识别库
- 支持从可配置地址在线更新完整运行配置
- 支持按 Git 提交号手动检查程序新版本
- 支持 CPU、内存、温度、系统负载和 AP 数趋势

## 运行环境

推荐环境：

- Linux
- 推荐 Raspberry Pi OS
- 使用 `linux-arm64` 发布产物时需要 64 位系统
- 支持监控模式的无线网卡
- 切换监控模式 / 信道时需要 root 权限
- 使用 AP 热点网页服务时需要 `iw` 和 `hostapd`

部署 Linux 二进制文件：

```bash
install -m 0755 light_rid_scanner-linux-arm64 /opt/light-rid/light_rid_scanner
```

首次启动只需要放置二进制文件。`rid_config.json` 和 `rid_models.json` 不存在时，程序会在启动时按内置默认值自动创建。

```text
/opt/light-rid/light_rid_scanner
```

systemd 应直接执行二进制文件：

```ini
ExecStart=/opt/light-rid/light_rid_scanner --config /opt/light-rid/rid_config.json --no-tui
```

默认网页地址：

- `http://<设备IP>:4600/`

## 固定网卡绑定与 OOBE

- 扫描器不再自动递增轮换网卡。
- `basic.iface` 现在被视为固定绑定项；如果这张网卡不存在，服务会保持降级运行并提示配置，而不是悄悄切到别的网卡。
- `basic.lost_timeout` 用于配置飞机离线判定时间，默认 15 秒。
- OOBE 和设置页提供“自定义网卡绑定”，可以把每张网卡设置为 `scan`（扫描）、`web`（网页服务）、`ap_web`（AP 热点网页服务）、`disabled`（禁用）、`idle`（闲置）或 `none`；`scan` 会同步写回 `basic.iface`。
- `ap_web` 会通过 `hostapd` 配置热点，使用内置 DHCP 在 `172.16.0.0/24` 分配地址，并在服务具备所需 Linux capability 时把网页服务暴露到 `172.16.0.1:80`。
- 如果 `rid_config.json` 缺失、损坏，或者还没有绑定默认网卡，网页会进入 `/oobe` 初始化流程。
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
  源码和构建共用的薄入口。
- `light_rid/`
  拆分后的扫描、解析、HTTP/WS 服务、内嵌页面、API、设置、认证、硬件辅助和 CLI/TUI 模块。
- `light_rid_scanner`
  部署目标上的 Linux 单文件运行二进制。
- `rid_models.json`
  机型前缀映射表。
- `rid_config.example.json`
  可提交到 Git 的安全示例配置。
- `rid_config.json`
  实际运行配置，不应提交。
- `EULA.md`
  内置 EULA 同意页面显示的源文本。
- `rid_history_cache.json`
  运行时生成的历史 / 轨迹缓存。
- `rid_config.json.rollback`
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

- `rid_config.example.json`

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
curl -H "X-API-Token: YOUR_TOKEN" \
  http://0.0.0.0:4600/api/v1/snapshot
```

```bash
curl -H "Authorization: Bearer YOUR_TOKEN" \
  http://0.0.0.0:4600/api/v1/drones
```

### 如何启用外部 API

外部 API 只有在以下三个条件同时满足时才允许开启：

- 已启用网页登录鉴权
- 已配置网页登录账号和密码
- 已配置 API Token

```json
{
  "auth": {
    "enabled": true,
    "username_hash": "<scrypt(username)>",
    "password_hash": "<scrypt(password)>"
  },
  "api": {
    "enabled": true,
    "token": "YOUR_TOKEN_HERE",
    "token_hash": "<scrypt(token)>",
    "whitelist_enabled": true,
    "whitelist": [
      "127.0.0.1",
      "<trusted-lan-cidr>"
    ]
  }
}
```

生成和程序一致的 scrypt 哈希：

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
- `POST /api/notifications`
- `POST /api/notifications/delete`
- `POST /api/notifications/clear`
- `GET /api/settings/view`
- `GET /api/settings/runtime`
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
- `POST /api/tools/import/all`
- `POST /api/tools/import/track`
- `GET /api/tracks/get?sn=<SN>`
- `POST /api/tracks/clear`
- `POST /api/history/delete`
- `POST /api/history/clear`

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

设置页可以从远端 JSON 文件更新 `rid_models.json`。默认地址：

```text
https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/refs/heads/main/rid_models.json
```

行为说明：

- 启用后每天自动检查一次
- 手动更新按钮使用同一个地址
- 地址必须以 `http://` 或 `https://` 开头
- 更新成功或失败都会写入操作日志和通知中心
- 同一个设置卡片可以把 `rid_models.json` 作为前缀/机型列表编辑
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
- 二进制部署时，systemd 服务应始终指向已安装的 `light_rid_scanner` 二进制文件、当前配置文件路径以及 `--no-tui` 服务运行模式。

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

`rid_build_info.json` 保存当前 Git 短提交号和本地构建号。CI 工作流会生成用于部署的 Linux 单文件产物，其中 64 位 Raspberry Pi OS 使用 `light_rid_scanner-linux-arm64`。

设置页可以手动比较本地程序提交号和远端 Git 提交号。这个检查只报告是否存在更新，不会自动下载、套用代码或重启服务。

当前工作区准备发布的版本线是 `v2.0`，但页面仍继续使用上面的 commit 构建标记，便于定位每一次本地构建。

## 通知中心

通知中心现在由服务端提供数据，不再依赖浏览器本地缓存。最近通知保存在服务进程内存中，并通过 `/api/notifications` 提供给所有打开的浏览器会话。

当前通知来源包括：

- 飞机上线 / 离线事件
- 报警区域事件
- 识别库更新结果
- 内置页面提交的手动通知

通知可以单条删除，也可以在页面上一键清空。

## 日志页

打开方式：

- `/logs`

支持内容：

- 运行日志
- 操作 / 审计日志
- 完整扫描日志
- 运行日志与扫描日志的 unified diff
- 单项文本导出或全部 ZIP 导出
- API 文档查看
- 跳转到硬件助手

敏感字段在可视化模式下默认遮罩：

- 企业微信 Webhook Key
- API Token

如果这些输入框保持空白 / 保持遮罩状态，保存时会沿用当前已存值。

## 企业微信通知

现在支持多个机器人通道：

```json
{
  "notify": {
    "enabled": true,
    "send_timeout_sec": 8,
    "notify_reonline": true,
    "reonline_cooldown_sec": 300,
    "wecom_webhooks": [
      {
        "name": "默认通道",
        "enabled": true,
        "key": "YOUR_WEBHOOK_KEY"
      },
      {
        "name": "备用通道",
        "enabled": false,
        "key": "YOUR_SECOND_KEY"
      }
    ]
  }
}
```

行为说明：

- 飞机上线通知会发往所有启用通道
- 测试通知会发往所有启用通道
- 旧字段 `notify.wecom_webhook_key` 仍兼容

## 报警区域

现在支持多个矩形报警区域：

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

行为说明：

- 启用的区域会以红框显示在地图上
- 飞机进入区域时触发全屏网页报警
- 如果浏览器已授权，会同时弹出浏览器通知
- 旧字段 `web.alarm_zone` 仍兼容

## 硬件助手

直接打开：

- `/hardware-assistant`

支持操作：

- 列出无线网卡
- 查看 `iw dev`、`iw info`、`iw link`
- 切换监控 / 托管模式
- 重启网卡
- 设置信道
- 重启主程序

## 导入导出辅助接口

内置页面常用辅助接口：

- `GET /api/settings/export/settings`
- `GET /api/settings/export/scan-data`
- `POST /api/settings/import/settings`
- `POST /api/settings/import/scan-data`
- `GET /api/tools/export/all`
- `GET /api/tools/export/track?sn=<SN>`
- `POST /api/tools/import/all`
- `POST /api/tools/import/track`

## Git / 隐私规则

提交到 GitHub 之前请确保：

- 不要提交 `rid_config.json`
- 不要提交真实企业微信 Key
- 不要提交真实 API Token
- 不要提交运行期生成的历史 / 缓存文件
- 只提交 `rid_config.example.json`

## 说明

- 浏览器定位按钮是否可用，取决于浏览器安全策略；很多浏览器要求 HTTPS 或 localhost。
- 地图上的基站、报警区域、轨迹、飞机 / 飞手标记，都来自 `run.py` 的运行时状态。
- 如果要获取当前最准确的机器可读接口索引，优先使用 `GET /api/docs`。

## OpenDroneID 官方参考

- Open Drone ID Core C Library（官方库）: https://github.com/opendroneid/opendroneid-core-c
- OpenDroneID specs 仓库: https://github.com/opendroneid/specs
- specs 仓库已明确说明其中内容是早期草案；如果需要最终 ASTM Remote ID 标准文本，请直接从 ASTM 获取正式版 F3411。
