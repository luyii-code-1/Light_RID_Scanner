# Light RID Scanner

[English](README.md) | [简体中文](README.zh-CN.md)

Light RID Scanner 是一个面向树莓派和其他 Linux 采集节点的固定式 Remote ID / OpenDroneID Wi-Fi 监测器。

项目的运行模型保持得比较克制：核心逻辑集中在 `run.py`，重点放在长期稳定运行、受保护的配置写入、历史与轨迹持久化，以及适合局域网部署的 Web 界面。

## 功能概览

- 现代化局域网页面，分为三大主视图：
  - `地图`
  - `飞机列表`
  - `其他`（实时 AP 列表 + AP 扫描日志）
- 独立 `/settings` 设置页，支持可视化编辑
- 独立 `/hardware-assistant` 硬件助手页面
- 飞机历史与轨迹持久化
- 从 RID `System` 消息中提取飞手位置
- 支持导出全部详情和单机轨迹
- 支持 Token 保护的外部 API
- 支持网页登录 / 会话鉴权
- 企业微信支持多机器人通道
- 支持多个自定义报警区域并绘制到地图上

## 运行环境

推荐环境：

- Linux
- 推荐 Raspberry Pi OS
- Python 3.10+
- 支持监控模式的无线网卡
- 切换监控模式 / 信道时需要 root 权限

启动方式：

```bash
sudo ~/rid/.venv/bin/python3 run.py
```

程序现在默认就是无 TUI 模式，不再需要 `--no-tui`。

默认网页地址：

- `http://<设备IP>:4600/`

## 固定网卡绑定与 OOBE

- 扫描器不再自动递增轮换网卡。
- `basic.iface` 现在被视为固定绑定项；如果这张网卡不存在，服务会保持降级运行并提示配置，而不是悄悄切到别的网卡。
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
  可视化设置、原始配置编辑、通知设置、报警区域设置、API 说明。
- `/hardware-assistant`
  网卡状态、`iw` 检查、监控/托管模式切换、信道调整、网卡重启、主程序重启。

## 关键文件

- `run.py`
  主扫描器、解析器、HTTP/WS 服务、内嵌页面与 API 处理逻辑。
- `rid_models.json`
  机型前缀映射表。
- `rid_config.example.json`
  可提交到 Git 的安全示例配置。
- `rid_config.json`
  实际运行配置，不应提交。
- `rid_history_cache.json`
  运行时生成的历史 / 轨迹缓存。
- `rid_config.json.rollback`
  配置文件回滚副本。

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
  浏览器网页登录 / 会话鉴权。
- `api`
  外部 API 的 Token 鉴权。

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
  http://192.168.1.32:4600/api/v1/snapshot
```

```bash
curl -H "Authorization: Bearer YOUR_TOKEN" \
  http://192.168.1.32:4600/api/v1/drones
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
    "username_sha256": "<sha256(username)>",
    "password_sha256": "<sha256(password)>"
  },
  "api": {
    "enabled": true,
    "token": "YOUR_TOKEN_HERE",
    "token_sha256": "<sha256(token)>",
    "whitelist_enabled": true,
    "whitelist": [
      "127.0.0.1",
      "192.168.1.0/24"
    ]
  }
}
```

生成哈希的方法：

```bash
python3 - <<'PY'
import hashlib
print(hashlib.sha256(b"YOUR_TOKEN_HERE").hexdigest())
PY
```

如果你只保留 `api.token_sha256`，外部 API 仍然可用，但设置页面将无法显示或复制当前 Token，因为系统只拿到了哈希。

### 推荐使用方式

建议这样做：

- 在本地生成一个随机 Token
- 如果希望后续能在设置页里再次显示/复制 Token，就让 `api.token` 和 `api.token_sha256` 一起保存并保持一致
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
    "username_sha256": "<sha256(username)>",
    "password_sha256": "<sha256(password)>",
    "realm": "Light RID Scanner"
  }
}
```

生成用户名 / 密码哈希：

```bash
python3 - <<'PY'
import hashlib
print("user:", hashlib.sha256("your_user".encode()).hexdigest())
print("pass:", hashlib.sha256("your_pass".encode()).hexdigest())
PY
```

受信任的本地启动器可以使用 SSO 形式登录：

```text
/login?user=<sha256(username)>&password=<sha256(password)>
```

旧快捷方式如果写成逗号形式也能兼容：

```text
/login?user=<sha256(username)>,password=<sha256(password)>
```

### 只给网页会话用的辅助接口

这些接口主要给内置页面使用，依赖当前浏览器会话：

- `GET /api/settings/view`
- `GET /api/settings/runtime`
- `GET /api/settings/api-docs`
- `GET /api/logs/view?type=runtime|operation|scan|scan_diff|ap`
- `GET /api/logs/export?type=all|runtime|operation|scan|scan_diff|ap`
- `POST /api/settings/visual/save`
- `POST /api/settings/raw/save`
- `POST /api/settings/notify/test`
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

- 当前 API Token 会以密码框遮罩显示
- 显示或复制前，必须再次输入网页登录账号和密码
- 这次再次验证沿用网页登录凭据；外部 API 开启后仍必须使用 API Token
- 登录、Token 显示/复制、外部 API Token 失败都会触发内存限流，并写入操作日志。

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
- 原始 `rid_config.json` 编辑

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
