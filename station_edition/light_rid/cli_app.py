PACKET_PARSE_QUEUE_MAX = 4096
PACKET_PARSE_WORKERS = 12
packet_parse_queue = queue.Queue(maxsize=PACKET_PARSE_QUEUE_MAX)
packet_parse_drop_count = 0
packet_parse_worker_started = False
packet_parse_active_lock = Lock()
packet_parse_active_count = 0
RID_PARSE_FORMATS = {"GB46750_2025", "DJI_OLD_ODID"}
RID_PARSE_SN_RE = re.compile(r"^[A-Za-z0-9]{4,64}$")


def _rid_parser_sn_valid(value) -> bool:
    try:
        text = str(value or "").strip()
    except Exception:
        return False
    return bool(text and RID_PARSE_SN_RE.fullmatch(text))


def _rid_parser_has_coord(decoded: dict | None) -> bool:
    if not isinstance(decoded, dict):
        return False
    loc = decoded.get("location") if isinstance(decoded.get("location"), dict) else None
    if loc and _coord_pair_valid(loc.get("lat"), loc.get("lon")):
        return True
    sys_loc = decoded.get("system") if isinstance(decoded.get("system"), dict) else None
    if sys_loc and _coord_pair_valid(sys_loc.get("pilot_lat"), sys_loc.get("pilot_lon")):
        return True
    meta = decoded.get("metadata") if isinstance(decoded.get("metadata"), dict) else {}
    for key in ("operator_positions", "raw_coords"):
        for item in list(meta.get(key) or []):
            if not isinstance(item, dict):
                continue
            if _coord_pair_valid(item.get("lat"), item.get("lon")):
                return True
    return False


def _rid_parser_hint(pkt_bytes: bytes, ssid_rid: str | None, payloads: list[bytes], gb_payloads: list) -> bool:
    if ssid_rid:
        return True
    if gb_payloads or payloads:
        return True
    raw = bytes(pkt_bytes or b"")
    return (DJI_RID_VENDOR_PREFIX in raw) or (ODID_OUI in raw)


def _packet_clone_for_parse(pkt):
    try:
        return pkt.copy()
    except Exception:
        return pkt


def _packet_parse_drop_one() -> bool:
    try:
        packet_parse_queue.get_nowait()
        return True
    except queue.Empty:
        return False


def _enqueue_packet_for_parse(pkt) -> None:
    global packet_parse_drop_count
    item = _packet_clone_for_parse(pkt)
    while True:
        try:
            packet_parse_queue.put_nowait(item)
            _packet_parse_diag_note_queue(packet_parse_queue.qsize())
            return
        except queue.Full:
            dropped = _packet_parse_drop_one()
            if not dropped:
                return
            packet_parse_drop_count += 1
            if packet_parse_drop_count == 1 or (packet_parse_drop_count % 50) == 0:
                _log(
                    f"[WARN] packet parse queue full, dropped {packet_parse_drop_count} frame(s); "
                    f"queue={packet_parse_queue.qsize()}/{PACKET_PARSE_QUEUE_MAX}"
                )


def _packet_parse_worker_loop() -> None:
    global packet_parse_active_count
    while True:
        pkt = packet_parse_queue.get()
        started_at = time.perf_counter()
        queue_depth = packet_parse_queue.qsize()
        with packet_parse_active_lock:
            packet_parse_active_count += 1
        try:
            _parse_frame_impl(pkt)
        except Exception as ex:
            if DEBUG_MODE:
                _scan(f"[ERR] parse worker: {ex}")
        finally:
            with packet_parse_active_lock:
                packet_parse_active_count = max(0, packet_parse_active_count - 1)
            _packet_parse_diag_note_parse((time.perf_counter() - started_at) * 1000.0, queue_depth=queue_depth)


def start_packet_parse_worker() -> None:
    global packet_parse_worker_started
    if packet_parse_worker_started:
        return
    packet_parse_worker_started = True
    for _ in range(PACKET_PARSE_WORKERS):
        Thread(target=_packet_parse_worker_loop, daemon=True).start()


def parse_frame(pkt) -> None:
    _enqueue_packet_for_parse(pkt)


def _parse_frame_impl(pkt) -> None:
    global ap_seq
    try:
        if simulation_scan_pause_event.is_set():
            return
        if not pkt.haslayer(Dot11): return
        d11 = pkt[Dot11]
        if d11.type != 0: return
        _sniff_note_packet()
        if d11.subtype not in (8, 5, 13): return
        subtype_name = {8:"Beacon",5:"ProbeResp",13:"Action"}.get(d11.subtype,"Mgmt")

        src_mac = d11.addr2 or "unknown"
        rssi    = None
        if pkt.haslayer(RadioTap):
            try: rssi = pkt[RadioTap].dBm_AntSignal
            except Exception: pass

        rt_ch     = _rt_channel(pkt)
        ch        = rt_ch or current_channel
        ch_assumed = (rt_ch is None)
        now       = time.monotonic()

        # SSID 提取
        ssid = None
        if pkt.haslayer(Dot11Beacon):
            try:
                elt = pkt[Dot11Beacon].payload
                while elt and elt.name != "NoPayload":
                    if hasattr(elt,"ID") and elt.ID==0:
                        ssid = bytes(elt.info).decode("utf-8", errors="replace")
                        sn_s = _ssid_to_sn(ssid)
                        if sn_s: mac_to_ssid_sn[src_mac]={"sn":sn_s,"ts":now}
                        break
                    elt = elt.payload
            except Exception: pass
            # AP scan logs (for HTTP log panel)
            ts    = time.strftime("%H:%M:%S")
            rssi_s = f"{rssi}dBm" if rssi is not None else "N/A"
            ch_s2  = f"ch{ch}" if ch else "ch?"
            ssid_s = ssid or "(hidden)"
            with log_lock:
                ap_buf.append(f"[{ts}] {src_mac}  {rssi_s:>8}  {ch_s2:<5}  {ssid_s}")
                ap_seq += 1
            try:
                _ap_touch(src_mac, ssid, rssi, ch, "Beacon")
            except Exception:
                pass

        # Parse GB46750_2025 vendor bodies before legacy DJI ODID fragments.
        payloads = extract_from_ies(pkt)
        ssid_rid = _ssid_to_sn(ssid or "")
        gb_payloads = extract_gb46750_from_ies(pkt, ssid_rid) if d11.subtype == 8 else []
        gb_frame = bool(gb_payloads)
        if d11.subtype in (13, 5, 8):   # Extra: also scan raw payload for all mgmt subtypes
            raw_p = extract_from_raw(pkt)
            # 去重
            sigs = {zlib.crc32(p)&0xFFFFFFFF for p in payloads}
            for p in raw_p:
                if (zlib.crc32(p)&0xFFFFFFFF) not in sigs:
                    payloads.append(p)
            if d11.subtype == 8:
                gb_raw = extract_gb46750_from_raw(pkt, ssid_rid)
                gb_sigs = {_gb_payload_sig(p[0]) for p in gb_payloads}
                for p in gb_raw:
                    sig = _gb_payload_sig(p[0])
                    if sig not in gb_sigs:
                        gb_sigs.add(sig)
                        gb_payloads.append(p)
                if ssid_rid:
                    try:
                        gb_frame = bool(gb_payloads or (DJI_RID_VENDOR_PREFIX in bytes(pkt)))
                    except Exception:
                        gb_frame = bool(gb_payloads)
        if gb_frame and payloads:
            # GB46750 DJI vendor bodies contain byte sequences that
            # can look like legacy ODID fragments. Keep both parser paths
            # separate so those fragments cannot create fake positions.
            payloads = []

        # Debug scan logs
        if DEBUG_MODE:
            rssi_s  = f"{rssi}dBm" if rssi is not None else "N/A"
            ch_s    = f"{'~' if ch_assumed else ''}ch{ch}" if ch else "ch?"
            ssid_s  = f" SSID={ssid!r}" if ssid else ""
            odid_s  = ""
            if payloads:
                types = [f"{((p[0]>>4)&0xF):X}" for p in payloads if p]
                odid_s = f" ODID={len(payloads)}[{','.join(types)}]"
            if gb_payloads:
                odid_s += f" GB46750={len(gb_payloads)}"
            _scan(f"[FRAME] {subtype_name} src={src_mac} {rssi_s} {ch_s}{ssid_s}{odid_s}")

        is_wifi_fast = bool(SCAN_WIFI_FAST) and _is_wifi_fast_mac(src_mac)
        pkt_bytes = b""
        try:
            pkt_bytes = bytes(pkt)
        except Exception:
            pkt_bytes = b""
        rid_parser_hint = _rid_parser_hint(pkt_bytes, ssid_rid, payloads, gb_payloads)
        if not rid_parser_hint:
            payloads = []
            gb_payloads = []
        frame_hex = ""
        try:
            frame_hex = _hex_preview(pkt_bytes, max_bytes=220)
        except Exception:
            frame_hex = ""
        parsed_packets = []
        if rid_parser_hint:
            try:
                parsed_batch = parse_rid_payloads(
                    pkt_bytes,
                    mode="auto",
                    ssid_sn=(ssid_rid or None),
                    model_hint=None,
                )
                parsed_packets = list(parsed_batch.get("packets") or []) if parsed_batch.get("ok") else []
            except Exception:
                parsed_packets = []

        if parsed_packets:
            _notify_hit(ch if not ch_assumed or ch == current_channel else 0)
            for parsed in parsed_packets:
                if not isinstance(parsed, dict):
                    continue
                decoded = parsed.get("decoded") if isinstance(parsed.get("decoded"), dict) else rid_parse_result_to_decoded(parsed)
                if not isinstance(decoded, dict):
                    continue
                fmt = str(parsed.get("format") or "")
                sn = str(parsed.get("sn") or ((decoded.get("basic_id") or {}).get("uas_id") or "")).strip()
                if fmt not in RID_PARSE_FORMATS or not _rid_parser_sn_valid(sn) or not _rid_parser_has_coord(decoded):
                    continue
                body_hex = str(parsed.get("body_hex") or "")
                try:
                    body_bytes = bytes.fromhex(body_hex) if body_hex else bytes(pkt)
                except Exception:
                    body_bytes = bytes(pkt)
                sig = zlib.crc32(body_bytes) & 0xFFFFFFFF
                state_update(
                    src_mac,
                    decoded,
                    rssi=rssi,
                    ch=ch,
                    ch_assumed=ch_assumed,
                    pl_sig=sig,
                    scan_type=("phone" if is_wifi_fast else "rid"),
                    ssid=ssid,
                    capture_type=subtype_name,
                    raw_pkt_hex=(body_hex or frame_hex),
                    firmware_type=("new" if fmt == "GB46750_2025" else "old"),
                )
                if DEBUG_MODE:
                    b = decoded.get("basic_id")
                    l = decoded.get("location")
                    s = decoded.get("system")
                    if b: _scan(f"  -> Parsed BasicID: {b}")
                    if l and l.get("lat") is not None and l.get("lon") is not None:
                        _scan(f"  -> Parsed Location: lat={l.get('lat'):.5f} lon={l.get('lon'):.5f}")
                    if s and s.get("pilot_lat") is not None and s.get("pilot_lon") is not None:
                        _scan(f"  -> Parsed System: lat={s.get('pilot_lat'):.5f} lon={s.get('pilot_lon'):.5f}")
            return

        if not payloads and not gb_payloads:
            # Even without ODID payload, if SSID contains RID SN, still refresh last_seen_ts.
            if is_wifi_fast:
                state_update(src_mac, {"basic_id": {"uas_id": _wifi_fast_sn(src_mac), "id_type": "SSID"}, "location": None, "system": None},
                             rssi=rssi, ch=ch, ch_assumed=ch_assumed, pl_sig=0,
                             scan_type="phone", ssid=(ssid or ""), capture_type=subtype_name,
                             raw_pkt_hex=frame_hex, firmware_type="old")
            elif ssid and src_mac in mac_to_ssid_sn:
                state_update(src_mac, {"basic_id": None, "location": None, "system": None},
                             rssi=rssi, ch=ch, ch_assumed=ch_assumed, pl_sig=0,
                             scan_type="rid", ssid=ssid, capture_type=subtype_name,
                             raw_pkt_hex=frame_hex, firmware_type="old")
            return

        _notify_hit(ch if not ch_assumed or ch==current_channel else 0)

        def explode(p: bytes) -> list[bytes]:
            if not p: return []
            mt = (p[0]>>4)&0xF
            if mt != MSG_TYPE_PACK:
                return [p[:ODID_MSG_SIZE]] if len(p)>=ODID_MSG_SIZE else [p]
            layout = _decode_odid_pack_layout(p)
            if not layout:
                return [p]
            base, msg_size, qty = layout
            out = []
            for i in range(qty):
                s, e2 = base + i * msg_size, base + (i + 1) * msg_size
                if e2 <= len(p): out.append(p[s:e2])
            return out or [p]

        for payload in payloads:
            if not payload: continue
            for piece in explode(payload):
                sig     = zlib.crc32(piece if len(piece)>=ODID_MSG_SIZE else payload)&0xFFFFFFFF
                decoded = decode_odid(piece)
                if is_wifi_fast and not (decoded.get("basic_id") and decoded.get("basic_id", {}).get("uas_id")):
                    decoded = {
                        "basic_id": {"uas_id": _wifi_fast_sn(src_mac), "id_type": "SSID"},
                        "location": decoded.get("location"),
                        "system": decoded.get("system"),
                    }
                if not is_wifi_fast:
                    decoded["metadata"] = {
                        "format": "DJI_OLD_ODID",
                        "rid_format": "DJI_OLD_ODID",
                        "dji_rid_kind": "DJI_OLD_ODID",
                    }
                    legacy_sn = str(((decoded.get("basic_id") or {}).get("uas_id")) or ssid_rid or mac_to_basic.get(src_mac, {}).get("basic", {}).get("uas_id") or "").strip()
                    if not _rid_parser_sn_valid(legacy_sn) or not _rid_parser_has_coord(decoded):
                        continue
                state_update(src_mac, decoded, rssi=rssi, ch=ch,
                             ch_assumed=ch_assumed, pl_sig=sig,
                             scan_type=("phone" if is_wifi_fast else "rid"),
                             ssid=ssid, capture_type=subtype_name,
                             raw_pkt_hex=_hex_preview(piece if piece else payload, max_bytes=160),
                             firmware_type="old")
                if DEBUG_MODE:
                    b = decoded.get("basic_id")
                    l = decoded.get("location")
                    s = decoded.get("system")
                    if b: _scan(f"  -> BasicID: {b}")
                    if l: _scan(f"  -> Location: lat={l.get('lat'):.5f} lon={l.get('lon'):.5f} "
                                f"alt={l.get('alt_geodetic'):.1f}m spd={l.get('speed_ms')}")
                    if s: _scan(f"  -> System(pilot): lat={s.get('pilot_lat')} lon={s.get('pilot_lon')} type={s.get('pilot_loc_type_text')}")
        for body, decoded in gb_payloads:
            if not body or not decoded:
                continue
            meta = decoded.get("metadata") if isinstance(decoded.get("metadata"), dict) else {}
            gb_sn = str(((decoded.get("basic_id") or {}).get("uas_id")) or ssid_rid or "").strip()
            gb_fmt = str(meta.get("format") or meta.get("rid_format") or "")
            if gb_fmt not in RID_PARSE_FORMATS or not _rid_parser_sn_valid(gb_sn) or not _rid_parser_has_coord(decoded):
                continue
            sig = _gb_payload_sig(body)
            state_update(src_mac, decoded, rssi=rssi, ch=ch,
                         ch_assumed=ch_assumed, pl_sig=sig,
                         scan_type="rid", ssid=ssid, capture_type=subtype_name,
                         raw_pkt_hex=_hex_preview(body, max_bytes=160),
                         firmware_type="new")
            if DEBUG_MODE:
                b = decoded.get("basic_id")
                l = decoded.get("location")
                if b: _scan(f"  -> GB BasicID: {b}")
                if l and l.get("lat") is not None and l.get("lon") is not None:
                    _scan(f"  -> GB Location: lat={l.get('lat'):.5f} lon={l.get('lon'):.5f} "
                          f"alt={l.get('alt_geodetic')}m")
    except Exception as ex:
        if DEBUG_MODE:
            _scan(f"[ERR] parse_frame: {ex}")

# -----------------------------------------------------------------------------
# TUI -curses
# -----------------------------------------------------------------------------

# Column definition: (header text, display width, field key)
COLUMNS = [
    ("●",    2, "dot"),
    ("SN",  22, "sn_s"),
    ("机型", 12, "model"),
    ("ch",   5, "ch_s"),
    ("纬度", 11, "lat_s"),
    ("经度", 11, "lon_s"),
    ("高程",  8, "alt_s"),
    ("速度",  8, "spd_s"),
    ("垂速",  7, "vsp_s"),
    ("信号",  8, "rssi_s"),
    ("包",    6, "pkts"),
    ("方向",  4, "dir_s"),
    ("时效",  7, "age_s"),
]

def _entry_row(e: dict, now: float) -> dict:
    age  = now - e.get("last_seen_ts", now)
    lost = age > LOST_TIMEOUT
    ch   = e.get("last_ch") or 0
    sn   = str(e.get("sn",""))
    return {
        "dot":     "○" if lost else "●",
        "lost":    lost,
        "mac_only": sn.startswith("MAC:"),
        "sn_s":    (sn[:20]+"...") if len(sn)>21 else sn,
        "model":   str(e.get("model","N/A")),
        "ch_s":    f"{'~' if e.get('ch_assumed') else ''}{ch}" if ch else "?",
        "lat_s":   _fmt(e.get("lat"),".5f"),
        "lon_s":   _fmt(e.get("lon"),".5f"),
        "alt_s":   _fmt(e.get("alt"),".1f","m"),
        "spd_s":   _fmt(e.get("speed"),".1f","m/s"),
        "vsp_s":   _fmt(e.get("vspeed"),".1f"),
        "rssi_s":  _fmt(e.get("rssi"),"d","dBm"),
        "pkts":    str(e.get("pkt_count",0)),
        "dir_s":   e.get("move_dir") or "-",
        "age_s":   f"{age:.0f}s",
    }

def tui_main(stdscr, args) -> None:
    curses.curs_set(0)
    stdscr.nodelay(True)
    curses.start_color()
    curses.use_default_colors()

    curses.init_pair(1, curses.COLOR_GREEN,  -1)   # 在线 SN
    curses.init_pair(2, curses.COLOR_YELLOW, -1)   # MAC-only
    curses.init_pair(3, curses.COLOR_WHITE,  -1)   # 离线
    curses.init_pair(4, curses.COLOR_CYAN,   -1)   # 表头
    curses.init_pair(5, curses.COLOR_BLACK,  curses.COLOR_CYAN)  # title bar
    curses.init_pair(6, curses.COLOR_YELLOW, -1)                 # 变化高亮

    C_ONLINE  = curses.color_pair(1) | curses.A_BOLD
    C_MACONLY = curses.color_pair(2)
    C_LOST    = curses.color_pair(3) | curses.A_DIM
    C_HEADER  = curses.color_pair(4) | curses.A_BOLD
    C_TITLE   = curses.color_pair(5) | curses.A_BOLD
    C_HL      = curses.color_pair(6) | curses.A_BOLD

    # mode: "table" | "log"（事件日志） | "scan"（完整扫描日志）
    mode       = "table"
    log_offset = 0
    last_draw  = 0.0

    while True:
        now = time.monotonic()
        h, w = stdscr.getmaxyx()

        try:
            key = stdscr.getch()
        except curses.error:
            key = -1

        if key in (ord('q'), ord('Q')):
            break
        elif key in (ord('d'), ord('D')):
            if mode == "table":
                mode = "scan"       # First press `d`: scan log
            elif mode == "scan":
                mode = "log"        # Second press `d`: event log
            else:
                mode = "table"      # Third press `d`: back to table
            log_offset = 0
        elif key == curses.KEY_UP:
            if mode != "table": log_offset = min(log_offset+3, LOG_BUF_SIZE-1)
        elif key == curses.KEY_DOWN:
            if mode != "table": log_offset = max(log_offset-3, 0)
        elif key in (ord('g'), curses.KEY_HOME, ord('G'), curses.KEY_END):
            log_offset = 0

        if (now - last_draw) < TUI_REFRESH and key == -1:
            time.sleep(0.03)
            continue
        last_draw = now

        stdscr.erase()

        # -- title bar ------------------------------------------------------
        with state_lock:
            n_total = len(state_table)
            n_live  = sum(1 for e in state_table.values()
                         if (now-e["last_seen_ts"]) <= LOST_TIMEOUT)
        ch_s    = f"ch{current_channel}" if current_channel else "ch?"
        dbg_s   = " [DEBUG]" if DEBUG_MODE else ""
        mode_lbl = {"table":"table","scan":"scan-log","log":"events"}.get(mode,"?")
        left  = f"  RID Monitor  LIVE={n_live}  LOST={n_total-n_live}  {ch_s}{dbg_s} "
        right = f" [d]{mode_lbl}  [↑↓]scroll  [q]quit "
        bar   = left.ljust(w - _sw(right)) + right
        try: stdscr.addstr(0, 0, _pad(bar, w), C_TITLE)
        except curses.error: pass

        if mode == "table":
            _draw_table(stdscr, h, w, now, C_HEADER, C_ONLINE, C_MACONLY, C_LOST, C_HL)
        elif mode == "scan":
            _draw_buf(stdscr, h, w, scan_buf, log_offset, "scan log (all frames)", "d->events d->table")
        else:
            _draw_buf(stdscr, h, w, log_buf,  log_offset, "事件日志", "d->表格")

        try: stdscr.refresh()
        except curses.error: pass

def _draw_table(stdscr, h, w, now, C_HEADER, C_ONLINE, C_MACONLY, C_LOST, C_HL):
    # 表头
    hdr = ""
    for label, width, _ in COLUMNS:
        hdr += _pad(label, width) + " "
    sep = "-" * min(w, _sw(hdr))
    try:
        stdscr.addstr(1, 0, hdr[:w], C_HEADER)
        stdscr.addstr(2, 0, sep[:w], C_HEADER)
    except curses.error: pass

    with state_lock:
        entries = sorted(
            state_table.values(),
            key=lambda e: (
                (now-e["last_seen_ts"]) > LOST_TIMEOUT,
                -(e.get("rssi") or -999),
            )
        )

    row_y = 3
    for e in entries:
        if row_y >= h-1: break
        r  = _entry_row(e, now)
        hl = e.get("_hl", {})   # {col_key: expire_monotonic}
        if r["lost"]:       base_attr = C_LOST
        elif r["mac_only"]: base_attr = C_MACONLY
        else:               base_attr = C_ONLINE

        col_x = 0
        for _, width, key in COLUMNS:
            cell  = _pad(str(r.get(key,"")), width) + " "
            # Highlight this column if it has unexpired change mark.
            attr  = C_HL if (not r["lost"] and hl.get(key, 0) > now) else base_attr
            try: stdscr.addstr(row_y, col_x, cell, attr)
            except curses.error: pass
            col_x += width + 1
            if col_x >= w: break

        row_y += 1

    hint = f" total={len(entries)} refresh~{TUI_REFRESH:.1f}s "
    try: stdscr.addstr(h-1, 0, hint[:w].ljust(w), curses.A_DIM)
    except curses.error: pass

def _draw_buf(stdscr, h, w, buf: deque, offset: int, title: str, hint_extra: str):
    with log_lock:
        lines = list(buf)
    vis     = h - 2
    total   = len(lines)
    end_i   = max(0, total - offset)
    start_i = max(0, end_i - vis)
    for i, line in enumerate(lines[start_i:end_i]):
        if 1+i >= h-1: break
        try: stdscr.addstr(1+i, 0, line[:w].ljust(min(w, len(line)+4)))
        except curses.error: pass
    hint = f" {title} [{start_i+1}-{end_i}/{total}]  scroll ↑↓  {hint_extra} "
    try: stdscr.addstr(h-1, 0, hint[:w].ljust(w), curses.A_DIM)
    except curses.error: pass

# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------
def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="OpenDroneID RID WLAN listener")
    parser.add_argument("--config", default=os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT),
                        help="config file path (default: config.json)")
    parser.add_argument("--iface",        default=None)
    parser.add_argument("--channel",      default=None, type=int)
    parser.add_argument("--hop",          action="store_true")
    parser.add_argument("--hop-5g",       action="store_true")
    parser.add_argument("--scan-wifi-fast", action="store_true")
    parser.add_argument("--dwell-2g",     default=DWELL_2G_DEFAULT, type=int)
    parser.add_argument("--dwell-5g",     default=DWELL_5G_DEFAULT, type=int)
    parser.add_argument("--settle",       default=SETTLE_DEFAULT,   type=int)
    parser.add_argument("--dwell-on-hit", default=2500, type=int)
    parser.add_argument("--hit-cap",      default=6000, type=int)
    parser.add_argument("--time",         default=DEFAULT_PRINT_INTERVAL, type=float,
                        help="heartbeat interval seconds (default 2.0)")
    parser.add_argument("--min-gap",      default=DEFAULT_MIN_GAP, type=float,
                        help="minimum output gap for same SN (default 1.0)")
    parser.add_argument("--lost-timeout", default=DEFAULT_LOST_TIMEOUT, type=float,
                        help="aircraft offline threshold seconds (default 15)")
    parser.add_argument("--rssi-delta",   default=3, type=int)
    parser.add_argument("--change-on-rssi",    action="store_true")
    parser.add_argument("--change-on-payload", action="store_true")
    parser.add_argument("--model-map", default=os.path.join(os.getcwd(), MODEL_MAP_FILE_DEFAULT))
    parser.add_argument("--history-file", default=os.path.join(os.getcwd(), HISTORY_STORE_LEGACY_DEFAULT),
                        help="legacy history json path used only for migration into rid_storage.db")
    parser.add_argument("--no-tui",   action="store_true", default=True, help="禁用 TUI，纯文本输出")
    parser.add_argument("--tui",      action="store_false", dest="no_tui", help="启用 TUI")
    parser.add_argument("--debug",    action="store_true", help="write all raw frames into scan log")
    parser.add_argument("--notify-test", action="store_true", help="send one WeCom test notification then exit")
    parser.add_argument("--update-helper-plan", default="", help=argparse.SUPPRESS)
    return parser

_BASIC_CFG_ARG_DESTS = {
    "iface", "channel", "hop", "hop_5g", "scan_wifi_fast",
    "dwell_2g", "dwell_5g", "settle", "dwell_on_hit", "hit_cap",
    "time", "min_gap", "rssi_delta",
    "lost_timeout",
    "change_on_rssi", "change_on_payload",
    "model_map", "history_file",
    "no_tui", "debug",
}

def _parse_restart_args_text(args_text: str | None) -> tuple[list[str], str]:
    raw = str(args_text or "").strip()
    if not raw:
        return list(sys.argv[1:]), ""
    try:
        tokens = shlex.split(raw, posix=True)
    except ValueError as e:
        raise ValueError(f"参数解析失败: {e}")
    for t in tokens:
        opt = t.split("=", 1)[0]
        if opt in ("--notify-test", "--config"):
            raise ValueError(f"not allowed from web page: {opt}")
    return tokens, raw

def _merge_token_option(tokens: list[str], opt: str, value: str | None) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(tokens):
        t = str(tokens[i])
        if t == opt:
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if t.startswith(opt + "="):
            i += 1
            continue
        out.append(t)
        i += 1
    if value is not None and str(value).strip():
        out.extend([opt, str(value).strip()])
    return out

def _merge_token_flag(tokens: list[str], flag: str, enabled: bool) -> list[str]:
    out = [str(t) for t in tokens if str(t) != flag]
    if enabled:
        out.append(flag)
    return out

def _save_basic_config_from_tokens(tokens: list[str], raw_text: str = "", overrides: dict | None = None) -> tuple[bool, str]:
    global APP_CONFIG
    if not APP_CONFIG_PATH:
        return False, "config file path is empty"
    parser = build_arg_parser()
    try:
        ns = parser.parse_args(tokens)
    except SystemExit:
        return False, "invalid args"
    explicit = _parser_explicit_dests(parser, tokens)
    cfg = load_app_config(APP_CONFIG_PATH)
    basic = cfg.setdefault("basic", {})
    if not isinstance(basic, dict):
        basic = {}
        cfg["basic"] = basic
    for dest in _BASIC_CFG_ARG_DESTS:
        if dest in explicit:
            basic[dest] = getattr(ns, dest)
    if isinstance(overrides, dict):
        if "iface" in overrides:
            ov_iface = overrides.get("iface")
            basic["iface"] = (None if ov_iface in (None, "") else str(ov_iface).strip())
        if "scan_wifi_fast" in overrides:
            basic["scan_wifi_fast"] = _to_bool(overrides.get("scan_wifi_fast"), False)
    web = cfg.setdefault("web", {})
    if not isinstance(web, dict):
        web = {}
        cfg["web"] = web
    web["last_restart_args"] = raw_text if raw_text else " ".join(tokens)
    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="restart")
    if not b_ok:
        return False, f"backup failed: {backup_path}"
    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
    if ok:
        APP_CONFIG = cfg
        init_web_from_config(APP_CONFIG)
        init_ap_from_config(APP_CONFIG)
        init_notify_from_config(APP_CONFIG)
        return True, msg
    return False, msg

def _schedule_self_restart(tokens: list[str]) -> tuple[bool, str]:
    global restart_pending
    if not bool(WEB_CFG.get("allow_restart", True)):
        return False, "restart disabled"
    py = sys.executable or "python3"
    script = os.path.abspath(_runtime_entrypoint_path())
    if not os.path.exists(script):
        return False, f"script not found: {script}"
    exec_target = py
    exec_argv = [py] if getattr(sys, "frozen", False) else [py, script]
    with restart_lock:
        if restart_pending:
            return False, "已有重启任务"
        restart_pending = True

    def _do_restart(argv_tokens: list[str]) -> None:
        global restart_pending
        try:
            time.sleep(0.4)
            try:
                save_history_store(force=True)
            except Exception:
                pass
            try:
                os.chdir(APP_START_CWD)
            except Exception:
                pass
            argv_tokens = list(argv_tokens)
            has_cfg_arg = any(str(t).split("=", 1)[0] == "--config" for t in argv_tokens)
            if APP_CONFIG_PATH and (not APP_CONFIG_PATH_IS_DEFAULT) and not has_cfg_arg:
                argv_tokens.extend(["--config", APP_CONFIG_PATH])
            argv = exec_argv + argv_tokens
            _log("[INFO] 正在重启程序...")
            os.execv(exec_target, argv)
        except Exception as e:
            _log(f"[WARN] 程序重启失败: {e}")
            with restart_lock:
                restart_pending = False

    Thread(target=_do_restart, args=(list(tokens),), daemon=True).start()
    return True, "restarting"

def main() -> None:
    global PRINT_INTERVAL, MIN_GAP, LOST_TIMEOUT, CHANGE_ON_RSSI, CHANGE_ON_PL
    global RSSI_DELTA, NO_TUI, DEBUG_MODE, current_channel, HISTORY_STORE_PATH, APP_CONFIG
    global APP_CONFIG_PATH, APP_CONFIG_PATH_IS_DEFAULT, APP_CONFIG_PATH_LOCKED, APP_START_CWD
    global sniff_iface_name
    global SCAN_WIFI_FAST, WIFI_FAST_SUPPORTED, WIFI_FAST_SUPPORT_MSG

    try:
        if hasattr(sys.stdout,"reconfigure"):
            sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass

    parser = argparse.ArgumentParser(description="OpenDroneID RID WLAN listener")
    parser.add_argument("--config", default=os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT),
                        help="config file path (default: config.json)")
    parser.add_argument("--iface",        default=None)
    parser.add_argument("--channel",      default=None, type=int)
    parser.add_argument("--hop",          action="store_true")
    parser.add_argument("--hop-5g",       action="store_true")
    parser.add_argument("--scan-wifi-fast", action="store_true")
    parser.add_argument("--dwell-2g",     default=DWELL_2G_DEFAULT, type=int)
    parser.add_argument("--dwell-5g",     default=DWELL_5G_DEFAULT, type=int)
    parser.add_argument("--settle",       default=SETTLE_DEFAULT,   type=int)
    parser.add_argument("--dwell-on-hit", default=2500, type=int)
    parser.add_argument("--hit-cap",      default=6000, type=int)
    parser.add_argument("--time",         default=DEFAULT_PRINT_INTERVAL, type=float,
                        help="heartbeat interval seconds (default 2.0)")
    parser.add_argument("--min-gap",      default=DEFAULT_MIN_GAP, type=float,
                        help="minimum output gap for same SN (default 1.0)")
    parser.add_argument("--lost-timeout", default=DEFAULT_LOST_TIMEOUT, type=float,
                        help="aircraft offline threshold seconds (default 15)")
    parser.add_argument("--rssi-delta",   default=3, type=int)
    parser.add_argument("--change-on-rssi",    action="store_true")
    parser.add_argument("--change-on-payload", action="store_true")
    parser.add_argument("--model-map", default=os.path.join(os.getcwd(), MODEL_MAP_FILE_DEFAULT))
    parser.add_argument("--history-file", default=os.path.join(os.getcwd(), HISTORY_STORE_LEGACY_DEFAULT),
                        help="legacy history json path used only for migration into rid_storage.db")
    parser.add_argument("--no-tui",   action="store_true", default=True, help="禁用 TUI，纯文本输出")
    parser.add_argument("--tui",      action="store_false", dest="no_tui", help="启用 TUI")
    parser.add_argument("--debug",    action="store_true", help="write all raw frames into scan log")
    parser.add_argument("--notify-test", action="store_true", help="send one WeCom test notification then exit")
    parser.add_argument("--update-helper-plan", default="", help=argparse.SUPPRESS)
    APP_START_CWD = os.getcwd()
    args = parser.parse_args()

    if str(getattr(args, "update_helper_plan", "") or "").strip():
        raise SystemExit(_run_app_update_helper(str(args.update_helper_plan)))

    cfg_path = os.path.abspath(str(args.config)) if args.config else None
    APP_CONFIG_PATH = cfg_path
    APP_CONFIG_PATH_IS_DEFAULT = (cfg_path == os.path.abspath(os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT))) if cfg_path else True
    APP_CONFIG_PATH_LOCKED = any(str(t).split("=", 1)[0] == "--config" for t in sys.argv[1:])
    legacy_hist_path = os.path.abspath(str(args.history_file)) if args.history_file else None
    model_path = os.path.abspath(str(args.model_map)) if args.model_map else None
    hist_path = _history_store_default_path(cfg_path)
    _ensure_runtime_json_files(cfg_path, hist_path, config_locked=APP_CONFIG_PATH_LOCKED)
    APP_CONFIG = load_app_config(cfg_path)
    if not _eula_accepted():
        _log(f"[INFO] EULA pending: open /eula to accept ({_eula_set_path()})")
    apply_config_to_args(parser, args, APP_CONFIG)
    legacy_hist_path = os.path.abspath(str(args.history_file)) if args.history_file else legacy_hist_path
    model_path = os.path.abspath(str(args.model_map)) if args.model_map else None
    _ensure_runtime_json_files(None, hist_path, config_locked=True)
    _history_set_legacy_source_paths([legacy_hist_path])

    PRINT_INTERVAL  = max(0.2, float(args.time))
    MIN_GAP         = max(0.0, float(args.min_gap))
    LOST_TIMEOUT    = max(3.0, min(3600.0, float(args.lost_timeout)))
    CHANGE_ON_RSSI  = bool(args.change_on_rssi)
    CHANGE_ON_PL    = bool(args.change_on_payload)
    RSSI_DELTA      = max(1, int(args.rssi_delta))
    NO_TUI          = bool(args.no_tui)
    DEBUG_MODE      = bool(args.debug)
    SCAN_WIFI_FAST  = bool(args.scan_wifi_fast)
    HISTORY_STORE_PATH = hist_path

    # Redirect Python logging to `scan_buf` instead of `stderr` (avoids TUI swallow).
    class BufHandler(logging.Handler):
        def emit(self, record):
            _scan(f"[{record.levelname}] {self.format(record)}")
    root_logger = logging.getLogger()
    root_logger.setLevel(logging.DEBUG if DEBUG_MODE else logging.WARNING)
    root_logger.handlers.clear()
    root_logger.addHandler(BufHandler())

    init_web_from_config(APP_CONFIG)
    init_ap_from_config(APP_CONFIG)
    init_model_update_from_config(APP_CONFIG)
    init_config_update_from_config(APP_CONFIG)
    init_app_update_from_config(APP_CONFIG)
    init_metrics_from_config(APP_CONFIG)
    init_network_bindings_from_config(APP_CONFIG)
    init_auth_from_config(APP_CONFIG)
    init_api_from_config(APP_CONFIG)
    init_notify_from_config(APP_CONFIG)
    start_oui_loader()
    ensure_model_map_file(model_path or args.model_map)
    load_model_map(args.model_map)
    load_history_store(HISTORY_STORE_PATH)

    if args.notify_test:
        ok, resp = send_test_notification_from_config()
        if ok:
            _log("[INFO] WeCom notify test sent")
            if resp:
                _log(f"[INFO] WeCom response: {resp}")
        else:
            _log(f"[WARN] WeCom test notification failed: {resp}")
        return

    if hasattr(os, "geteuid") and os.geteuid() != 0:
        if _process_has_capabilities(list(RUNTIME_SERVICE_CAPABILITIES)):
            _log("[INFO] running without root; required network capabilities are present")
        else:
            _log("[WARN] 权限不足，请在设置页修复。")

    check_iw_available_on_startup()

    if SCAN_WIFI_FAST and (not args.hop) and (not args.channel):
        args.hop = True
        args.hop_5g = True
        _log("[INFO] WiFi fast-transfer scan enabled: auto use 2.4G+5G hopping")
    elif SCAN_WIFI_FAST and args.hop and (not args.hop_5g):
        args.hop_5g = True
        _log("[INFO] WiFi fast-transfer scan enabled: append 5G hopping")

    iface = interface_detect(prefer=args.iface)
    with sniff_health_lock:
        sniff_iface_name = str(iface or "")
    WIFI_FAST_SUPPORTED = False
    WIFI_FAST_SUPPORT_MSG = ""
    if iface:
        try:
            WIFI_FAST_SUPPORTED = bool(detect_5g(iface))
        except Exception:
            WIFI_FAST_SUPPORTED = False
        if SCAN_WIFI_FAST and WIFI_FAST_SUPPORTED:
            WIFI_FAST_SUPPORT_MSG = f"iface {iface} supports 5GHz; WiFi fast-transfer scan enabled"
        if SCAN_WIFI_FAST and not WIFI_FAST_SUPPORTED:
            WIFI_FAST_SUPPORT_MSG = f"iface {iface} does not support 5GHz; WiFi fast-transfer scan unavailable"
            _log(f"[WARN] {WIFI_FAST_SUPPORT_MSG}")
    else:
        WIFI_FAST_SUPPORT_MSG = NO_IFACE_DEGRADE_HINT
        _log(f"[WARN] {NO_IFACE_DEGRADE_HINT}")

    if args.hop and args.channel:
        _log("[WARN] --hop and --channel both set; using hopping mode")

    hop_cfg: tuple[list[int], list[int], int, int] | None = None
    if args.hop:
        dw2 = max(100, args.dwell_2g)
        dw5 = max(200, args.dwell_5g)
        hop_2g = CHANNELS_2G[:]
        hop_5g: list[int] = []
        if args.hop_5g:
            if WIFI_FAST_SUPPORTED:
                if SCAN_WIFI_FAST:
                    hop_5g = sorted(set(CHANNELS_5G + CHANNELS_5G_COMMON))
                else:
                    hop_5g = CHANNELS_5G[:]
                _log(f"[INFO] 5G channels={hop_5g}")
            else:
                _log("[INFO] 5G unsupported, using 2.4G only")
        hop_cfg = (hop_2g, hop_5g, dw2, dw5)
        _log(f"[INFO] hopping 2.4G={hop_2g}@{dw2}ms" + (f" 5G={hop_5g}@{dw5}ms" if hop_5g else ""))
        if iface:
            Thread(target=channel_hopper,
                   args=(iface, hop_2g, hop_5g, dw2, dw5,
                         max(0, args.settle), args.dwell_on_hit, args.hit_cap),
                   daemon=True).start()
        else:
            _log("[WARN] 无可用网卡，等待恢复…")
    elif args.channel:
        _log(f"[INFO] lock channel {args.channel}")
        if iface:
            run_cmd(f"iw dev {iface} set channel {args.channel}")
        else:
            _log("[WARN] 当前无网卡，先记录信道配置，网卡恢复后自动应用")
        current_channel = args.channel
    else:
        # Default lock to ch6 (DJI RID commonly used channel).
        _log("[INFO] default lock channel 6 (DJI RID common). Use --hop or --channel N to change")
        if iface:
            run_cmd(f"iw dev {iface} set channel 6")
        else:
            _log("[WARN] 当前无网卡，先使用默认信道配置，网卡恢复后自动应用")
        current_channel = 6

    _log(f"[INFO] output: first/changed(min-gap={MIN_GAP:.1f}s)/heartbeat(time={PRINT_INTERVAL:.1f}s)")
    _log(f"[INFO] LOST timeout={LOST_TIMEOUT:.0f}s  PURGE={PURGE_TIMEOUT:.0f}s")
    if DEBUG_MODE:
        _log("[INFO] DEBUG mode: all raw frames are written into scan log (press d)")

    Thread(target=lost_checker, daemon=True).start()
    Thread(target=http_server_thread, daemon=True).start()
    Thread(target=history_persist_loop, daemon=True).start()
    Thread(target=host_metrics_loop, daemon=True).start()
    start_packet_parse_worker()
    start_history_reparse_worker()
    start_hw_worker()
    start_notify_worker()
    start_model_update_worker()
    start_config_update_worker()
    start_app_update_check()
    _app_update_mark_startup_ready()

    def sniff_thread():
        global sniff_iface_name
        retry_delay = 2.0
        fail_count = 0
        recover_fail_count = 0
        iface_cur = str(iface or "")
        iface_watch_since = time.monotonic() if iface_cur else 0.0
        hop_started = bool(args.hop and bool(iface))
        simulation_was_paused = False

        def note_recover_failure(reason: str, allow_restart: bool = True) -> None:
            nonlocal recover_fail_count
            if (not allow_restart) or (not _cfg_auto_self_heal()):
                recover_fail_count = 0
                return
            recover_fail_count += 1
            _log(f"[WARN] sniff recover failed {recover_fail_count}/{SNIFF_RESTART_AFTER_FAILS}: {reason}")
            if recover_fail_count >= SNIFF_RESTART_AFTER_FAILS:
                _log("[WARN] sniff recover failed too many times, schedule self-restart")
                ok, msg = _schedule_self_restart(list(sys.argv[1:]))
                if not ok:
                    _log(f"[WARN] self-restart scheduling failed: {msg}")
                recover_fail_count = 0

        def note_recover_success() -> None:
            nonlocal recover_fail_count
            recover_fail_count = 0

        def set_iface_watch(iface_name: str) -> None:
            nonlocal iface_watch_since
            iface_watch_since = time.monotonic() if iface_name else 0.0

        while True:
            prefer_iface = _cfg_preferred_iface()
            if not iface_cur:
                iface_cur = _sniff_pick_iface(prefer=prefer_iface)
                if iface_cur:
                    set_iface_watch(iface_cur)
                    with sniff_health_lock:
                        sniff_iface_name = iface_cur
                    _log(f"[INFO] sniff iface recovered: {iface_cur}")
                    ok = _sniff_recover_iface(iface_cur, "iface connected", force=True)
                    if not ok:
                        _log(f"[WARN] sniff iface init failed: {iface_cur}, waiting retry")
                        iface_cur = ""
                        time.sleep(retry_delay)
                        continue
                    if args.hop and (not hop_started) and hop_cfg:
                        hop_2g, hop_5g, dw2, dw5 = hop_cfg
                        Thread(target=channel_hopper,
                               args=(iface_cur, hop_2g, hop_5g, dw2, dw5,
                                     max(0, args.settle), args.dwell_on_hit, args.hit_cap),
                               daemon=True).start()
                        hop_started = True
                    elif (not args.hop):
                        if current_channel:
                            run_cmd(f"iw dev {iface_cur} set channel {current_channel}")
                else:
                    _sniff_note_error(NO_IFACE_DEGRADE_HINT)
                    # Missing/unconfigured NIC should surface as a stable degraded state,
                    # not a self-restart loop.
                    note_recover_failure("no iface available", allow_restart=False)
                    _log(f"[WARN] sniff no available iface, retry in {retry_delay:.0f}s")
                    time.sleep(retry_delay)
                    continue

            try:
                with sniff_health_lock:
                    sniff_iface_name = iface_cur
                state, detail = _sniff_run_once(iface_cur, timeout_sec=SNIFF_POLL_TIMEOUT)
                if state == "hung":
                    _sniff_note_error(f"sniff worker hung: {detail}")
                    _log(f"[WARN] sniff worker hung on {iface_cur}: {detail}")
                    recovered = _sniff_recover_iface(iface_cur, f"worker hung: {detail}", force=True)
                    if not recovered:
                        new_iface = _sniff_pick_iface(prefer=(prefer_iface or iface_cur))
                        if new_iface and new_iface != iface_cur:
                            _log(f"[WARN] sniff iface switch after hang: {iface_cur} -> {new_iface}")
                            iface_cur = new_iface
                            set_iface_watch(iface_cur)
                            with sniff_health_lock:
                                sniff_iface_name = iface_cur
                            recovered = _sniff_recover_iface(iface_cur, "switch iface after hang", force=True)
                    if recovered:
                        set_iface_watch(iface_cur)
                        note_recover_success()
                    else:
                        note_recover_failure(f"worker hung on {iface_cur}", allow_restart=True)
                    time.sleep(retry_delay)
                    continue
                if state != "ok":
                    raise RuntimeError(detail or "sniff worker failed")
                fail_count = 0
                if simulation_scan_pause_event.is_set():
                    simulation_was_paused = True
                    set_iface_watch(iface_cur)
                    note_recover_success()
                    time.sleep(0.05)
                    continue
                if simulation_was_paused:
                    _sniff_note_resume()
                    set_iface_watch(iface_cur)
                    simulation_was_paused = False
                now_mono = time.monotonic()
                idle = _sniff_idle_sec(now_mono)
                no_pkt_elapsed = None
                if idle is None and iface_watch_since > 0.0:
                    no_pkt_elapsed = max(0.0, now_mono - iface_watch_since)
                stall_reason = None
                if idle is not None and idle >= SNIFF_STALL_RECOVER_SEC:
                    stall_reason = f"idle {idle:.0f}s without management frame"
                elif no_pkt_elapsed is not None and no_pkt_elapsed >= SNIFF_STALL_RECOVER_SEC:
                    stall_reason = f"no management frame for {no_pkt_elapsed:.0f}s after sniff start"
                if stall_reason:
                    recovered = _sniff_recover_iface(iface_cur, stall_reason, force=True)
                    if not recovered:
                        new_iface = _sniff_pick_iface(prefer=(prefer_iface or iface_cur))
                        if new_iface and new_iface != iface_cur:
                            _log(f"[WARN] sniff iface switch: {iface_cur} -> {new_iface}")
                            iface_cur = new_iface
                            set_iface_watch(iface_cur)
                            with sniff_health_lock:
                                sniff_iface_name = iface_cur
                            recovered = _sniff_recover_iface(iface_cur, "switch iface recovery", force=True)
                    if recovered:
                        set_iface_watch(iface_cur)
                        note_recover_success()
                    else:
                        note_recover_failure(stall_reason, allow_restart=True)
                else:
                    note_recover_success()
                time.sleep(0.05)
            except Exception as ex:
                fail_count += 1
                ex_msg = str(ex or "")
                _sniff_note_error(f"sniff exception#{fail_count}: {ex_msg}")
                no_dev_err = _sniff_is_no_device_error(ex)
                note_recover_failure(ex_msg, allow_restart=True)
                if _cfg_auto_self_heal() and (not no_dev_err) and fail_count >= SNIFF_RESTART_AFTER_FAILS:
                    _log(f"[WARN] sniff exception count reached {SNIFF_RESTART_AFTER_FAILS}, scheduling self-restart")
                    ok, msg = _schedule_self_restart(list(sys.argv[1:]))
                    if not ok:
                        _log(f"[WARN] self-restart scheduling failed: {msg}")
                    fail_count = 0

                if no_dev_err:
                    fail_count = 0
                    new_iface = _sniff_pick_iface(prefer=(prefer_iface or iface_cur))
                    if new_iface and new_iface != iface_cur:
                        _log(f"[WARN] sniff iface unavailable, switch {iface_cur} -> {new_iface}")
                        iface_cur = new_iface
                        set_iface_watch(iface_cur)
                        with sniff_health_lock:
                            sniff_iface_name = iface_cur
                        _sniff_recover_iface(iface_cur, f"after iface switch: {ex_msg}", force=True)
                    elif new_iface:
                        _log(f"[WARN] sniff iface exception#{fail_count}: {ex_msg}, try reset {iface_cur}")
                        if _sniff_recover_iface(iface_cur, f"exception#{fail_count}: {ex_msg}", force=True):
                            set_iface_watch(iface_cur)
                    else:
                        _log(f"[WARN] sniff iface lost: {ex_msg}, waiting for NIC recovery")
                        iface_cur = ""
                else:
                    _log(f"[WARN] sniff exception#{fail_count}: {ex_msg}, retry in {retry_delay:.0f}s")
                    _sniff_recover_iface(iface_cur, f"exception#{fail_count}: {ex_msg}", force=(fail_count >= 3))

                time.sleep(retry_delay)

    Thread(target=sniff_thread, daemon=True).start()

    if NO_TUI:
        _log("[INFO] --no-tui mode (Ctrl+C to exit)")
        try:
            while True: time.sleep(1)
        except KeyboardInterrupt:
            _log("[INFO] stopped")
        finally:
            save_history_store(force=True)
    else:
        if curses is None:
            raise SystemExit("curses is not available; install windows-curses on Windows or run with --no-tui")
        try:
            curses.wrapper(tui_main, args)
        except KeyboardInterrupt:
            pass
        finally:
            save_history_store(force=True)
            print("\n[INFO] TUI exited, last 30 event logs:")
            with log_lock:
                for line in list(log_buf)[-30:]:
                    print(line)
            if DEBUG_MODE:
                print("\n[INFO] Last 30 scan logs:")
                with log_lock:
                    for line in list(scan_buf)[-30:]:
                        print(line)

if __name__ == "__main__":
    main()
