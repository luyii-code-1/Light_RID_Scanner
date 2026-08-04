#![cfg_attr(not(target_os = "linux"), allow(dead_code))]

use crate::{
    parser::{self, ParseResult},
    state::{AppState, AppStateExt, DroneEntry, unix_now},
};
use serde_json::{Value, json};

#[derive(Debug, Clone)]
pub struct CaptureConfig {
    pub iface: String,
    pub phy: String,
    pub radio_device: String,
    pub channel: u16,
    pub prepare_monitor: bool,
    pub dedicate_radio: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrameMeta {
    pub source_mac: String,
    pub capture_type: &'static str,
    pub rssi: Option<i32>,
    pub channel: Option<u16>,
}

#[derive(Debug)]
struct MonitorFrame<'a> {
    meta: FrameMeta,
    dot11: &'a [u8],
}

pub fn spawn(state: AppState, config: CaptureConfig) {
    std::thread::Builder::new()
        .name("rid-capture".to_string())
        .spawn(move || run(state, config))
        .expect("start capture thread");
}

#[cfg(target_os = "linux")]
fn run(state: AppState, config: CaptureConfig) {
    use std::{ffi::CString, io, mem, os::fd::RawFd, process::Command, time::Duration};

    if config.prepare_monitor
        && let Err(error) = prepare_monitor(&config)
    {
        set_capture_error(&state, &config, format!("monitor setup failed: {error}"));
        return;
    }

    loop {
        match open_packet_socket(&config.iface) {
            Ok(fd) => {
                {
                    let mut status = state.capture.write();
                    status.running = true;
                    status.iface.clone_from(&config.iface);
                    status.channel = Some(config.channel);
                    status.last_error.clear();
                }
                state.log_info(format!(
                    "[INFO] native capture started iface={} channel={}",
                    config.iface, config.channel
                ));
                if let Err(error) = receive_loop(fd, &state) {
                    unsafe { libc::close(fd) };
                    set_capture_error(&state, &config, format!("capture failed: {error}"));
                }
            }
            Err(error) => set_capture_error(
                &state,
                &config,
                format!("open AF_PACKET socket failed: {error}"),
            ),
        }
        std::thread::sleep(Duration::from_secs(2));
    }

    fn command(program: &str, args: &[&str]) -> io::Result<()> {
        let output = Command::new(program).args(args).output()?;
        if output.status.success() {
            Ok(())
        } else {
            let detail = String::from_utf8_lossy(&output.stderr).trim().to_string();
            Err(io::Error::other(format!(
                "{program} {}: {detail}",
                args.join(" ")
            )))
        }
    }

    fn prepare_monitor(config: &CaptureConfig) -> io::Result<()> {
        if config.dedicate_radio {
            command("wifi", &["down", &config.radio_device])?;
        }
        let _ = command("iw", &["dev", &config.iface, "del"]);
        command(
            "iw",
            &[
                "phy",
                &config.phy,
                "interface",
                "add",
                &config.iface,
                "type",
                "monitor",
            ],
        )?;
        command("ip", &["link", "set", &config.iface, "up"])?;
        command(
            "iw",
            &[
                "dev",
                &config.iface,
                "set",
                "channel",
                &config.channel.to_string(),
                "HT20",
            ],
        )
    }

    fn open_packet_socket(iface: &str) -> io::Result<RawFd> {
        const ETH_P_ALL: u16 = 0x0003;
        let protocol = ETH_P_ALL.to_be() as i32;
        let fd = unsafe { libc::socket(libc::AF_PACKET, libc::SOCK_RAW, protocol) };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        let name = CString::new(iface)
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid interface name"))?;
        let index = unsafe { libc::if_nametoindex(name.as_ptr()) };
        if index == 0 {
            unsafe { libc::close(fd) };
            return Err(io::Error::last_os_error());
        }
        let address = libc::sockaddr_ll {
            sll_family: libc::AF_PACKET as u16,
            sll_protocol: ETH_P_ALL.to_be(),
            sll_ifindex: index as i32,
            sll_hatype: 0,
            sll_pkttype: 0,
            sll_halen: 0,
            sll_addr: [0; 8],
        };
        let rc = unsafe {
            libc::bind(
                fd,
                (&raw const address).cast::<libc::sockaddr>(),
                mem::size_of::<libc::sockaddr_ll>() as libc::socklen_t,
            )
        };
        if rc != 0 {
            let error = io::Error::last_os_error();
            unsafe { libc::close(fd) };
            return Err(error);
        }
        Ok(fd)
    }

    fn receive_loop(fd: RawFd, state: &AppState) -> io::Result<()> {
        let mut buffer = vec![0_u8; 8192];
        loop {
            let size = unsafe {
                libc::recv(
                    fd,
                    buffer.as_mut_ptr().cast::<libc::c_void>(),
                    buffer.len(),
                    0,
                )
            };
            if size < 0 {
                return Err(io::Error::last_os_error());
            }
            process_packet(state, &buffer[..size as usize]);
        }
    }
}

#[cfg(not(target_os = "linux"))]
fn run(state: AppState, config: CaptureConfig) {
    set_capture_error(
        &state,
        &config,
        "native capture is only available on Linux".to_string(),
    );
}

fn set_capture_error(state: &AppState, config: &CaptureConfig, error: String) {
    {
        let mut status = state.capture.write();
        status.running = false;
        status.iface.clone_from(&config.iface);
        status.channel = Some(config.channel);
        status.last_error.clone_from(&error);
    }
    state.log_info(format!("[WARN] {error}"));
}

fn process_packet(state: &AppState, raw: &[u8]) {
    {
        let mut status = state.capture.write();
        status.frames += 1;
        status.last_packet_ts = Some(unix_now());
    }
    let Some(frame) = decode_monitor_frame(raw) else {
        return;
    };
    state.capture.write().management_frames += 1;
    let packets = ingest_payload(state, frame.dot11, frame.meta, unix_now());
    if packets.is_empty() {
        return;
    }
    {
        let mut status = state.capture.write();
        status.rid_packets += packets.len() as u64;
        status.last_rid_ts = Some(unix_now());
    }
}

pub fn ingest_payload(
    state: &AppState,
    raw: &[u8],
    meta: FrameMeta,
    received_at: f64,
) -> Vec<ParseResult> {
    let packets = parser::parse_rid_packets(raw, Some("auto"));
    for packet in packets.iter().cloned() {
        ingest_packet(state, &meta, packet, received_at);
    }
    packets
}

fn ingest_packet(state: &AppState, meta: &FrameMeta, packet: ParseResult, now: f64) {
    if !packet.ok || packet.sn.is_empty() {
        state.capture.write().parse_errors += 1;
        return;
    }
    let position = packet.aircraft_position.as_ref();
    let lat = position
        .and_then(|item| item.get("lat"))
        .and_then(Value::as_f64);
    let lon = position
        .and_then(|item| item.get("lon"))
        .and_then(Value::as_f64);
    let alt = position
        .and_then(|item| item.get("alt"))
        .and_then(Value::as_f64);
    let speed = packet
        .decoded
        .get("location")
        .and_then(|item| item.get("speed_ms"))
        .and_then(Value::as_f64);
    let mut aircraft = Vec::new();
    let mut operator = Vec::new();
    for sample in &packet.track_samples {
        let mut value = json!(sample);
        value["timestamp_ms"] = json!((now * 1000.0) as i64);
        value["receive_time_ms"] = json!((now * 1000.0) as i64);
        if sample.track_type == "operator" {
            operator.push(value);
        } else {
            aircraft.push(value);
        }
    }
    let mut drones = state.drones.write();
    let entry = drones
        .entry(packet.sn.clone())
        .or_insert_with(|| DroneEntry {
            sn: packet.sn.clone(),
            src_mac: meta.source_mac.clone(),
            model: String::new(),
            lat,
            lon,
            alt,
            speed,
            rssi: meta.rssi,
            last_ch: meta.channel,
            capture_type: meta.capture_type.to_string(),
            firmware_type: if packet.format == "GB46750_2025" {
                "new"
            } else {
                "old"
            }
            .to_string(),
            scan_type: "rid".to_string(),
            pkt_count: 0,
            last_seen_wall_ts: now,
            tracks: json!({"aircraft": [], "operator": []}),
            simulation: false,
        });
    entry.src_mac.clone_from(&meta.source_mac);
    entry.lat = lat.or(entry.lat);
    entry.lon = lon.or(entry.lon);
    entry.alt = alt.or(entry.alt);
    entry.speed = speed.or(entry.speed);
    entry.rssi = meta.rssi.or(entry.rssi);
    entry.last_ch = meta.channel.or(entry.last_ch);
    entry.capture_type = meta.capture_type.to_string();
    entry.firmware_type = if packet.format == "GB46750_2025" {
        "new"
    } else {
        "old"
    }
    .to_string();
    entry.pkt_count += 1;
    entry.last_seen_wall_ts = now;
    append_tracks(&mut entry.tracks, "aircraft", aircraft);
    append_tracks(&mut entry.tracks, "operator", operator);
}

fn append_tracks(tracks: &mut Value, key: &str, mut incoming: Vec<Value>) {
    if incoming.is_empty() {
        return;
    }
    let Some(items) = tracks.get_mut(key).and_then(Value::as_array_mut) else {
        return;
    };
    items.append(&mut incoming);
    if items.len() > 512 {
        items.drain(0..items.len() - 512);
    }
}

fn decode_monitor_frame(raw: &[u8]) -> Option<MonitorFrame<'_>> {
    let (dot11_offset, rssi, channel) = parse_radiotap(raw).unwrap_or((0, None, None));
    let dot11 = raw.get(dot11_offset..)?;
    if dot11.len() < 24 {
        return None;
    }
    let frame_control = u16::from_le_bytes([dot11[0], dot11[1]]);
    let frame_type = (frame_control >> 2) & 0x3;
    if frame_type != 0 {
        return None;
    }
    let subtype = ((frame_control >> 4) & 0xf) as u8;
    let capture_type = match subtype {
        4 => "probe-request",
        5 => "probe-response",
        8 => "beacon",
        13 => "action",
        _ => "management",
    };
    let mac = &dot11[10..16];
    Some(MonitorFrame {
        meta: FrameMeta {
            source_mac: format!(
                "{:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
                mac[0], mac[1], mac[2], mac[3], mac[4], mac[5]
            ),
            capture_type,
            rssi,
            channel,
        },
        dot11,
    })
}

fn parse_radiotap(raw: &[u8]) -> Option<(usize, Option<i32>, Option<u16>)> {
    if raw.len() < 8 || raw[0] != 0 {
        return None;
    }
    let header_len = u16::from_le_bytes([raw[2], raw[3]]) as usize;
    if !(8..=raw.len()).contains(&header_len) {
        return None;
    }
    let first_present = u32::from_le_bytes([raw[4], raw[5], raw[6], raw[7]]);
    let mut present_offset = 4usize;
    while u32::from_le_bytes([
        *raw.get(present_offset)?,
        *raw.get(present_offset + 1)?,
        *raw.get(present_offset + 2)?,
        *raw.get(present_offset + 3)?,
    ]) & (1 << 31)
        != 0
    {
        present_offset += 4;
        if present_offset + 4 > header_len {
            return None;
        }
    }
    let mut cursor = present_offset + 4;
    let mut channel = None;
    let mut rssi = None;
    const FIELDS: [(usize, usize); 6] = [(8, 8), (1, 1), (1, 1), (2, 4), (2, 2), (1, 1)];
    for (index, (alignment, size)) in FIELDS.into_iter().enumerate() {
        if first_present & (1 << index) == 0 {
            continue;
        }
        cursor = align(cursor, alignment);
        let field = raw.get(cursor..cursor + size)?;
        if index == 3 {
            let frequency = u16::from_le_bytes([field[0], field[1]]);
            channel = frequency_to_channel(frequency);
        } else if index == 5 {
            rssi = Some(i8::from_ne_bytes([field[0]]) as i32);
        }
        cursor += size;
    }
    Some((header_len, rssi, channel))
}

fn align(value: usize, alignment: usize) -> usize {
    (value + alignment - 1) & !(alignment - 1)
}

fn frequency_to_channel(frequency: u16) -> Option<u16> {
    match frequency {
        2484 => Some(14),
        2412..=2472 => Some((frequency - 2407) / 5),
        5000..=5900 => Some((frequency - 5000) / 5),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_radiotap_and_management_header() {
        let mut frame = vec![0, 0, 14, 0, 0x28, 0, 0, 0, 0x85, 0x09, 0, 0, 0xd6, 0];
        frame.extend([0x80, 0x00, 0, 0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);
        frame.extend([0x8c, 0x1e, 0xd9, 0x03, 0x09, 0xb2]);
        frame.extend([0; 8]);
        let decoded = decode_monitor_frame(&frame).expect("management frame");
        assert_eq!(decoded.meta.source_mac, "8c:1e:d9:03:09:b2");
        assert_eq!(decoded.meta.capture_type, "beacon");
        assert_eq!(decoded.meta.rssi, Some(-42));
        assert_eq!(decoded.meta.channel, Some(6));
    }

    #[test]
    fn rejects_non_management_frames() {
        let mut frame = vec![0, 0, 8, 0, 0, 0, 0, 0];
        frame.extend([0x08, 0x00]);
        frame.extend([0; 22]);
        assert!(decode_monitor_frame(&frame).is_none());
    }

    #[test]
    fn ingests_rid_payload_into_station_state() {
        let state = crate::state::load("__missing_gl_ar750s_config.json", "__unused_history.json")
            .expect("state");
        let raw = parser::raw_packet_string_to_bytes(
            "fa0bbc0d24ff2048fffffe3135383146414e4c433235385530323952544e363030303030303030000101d1823b483bf2eb11ed0769833b4822f0eb1105001c00284700c2083d0902000c050478acc5529e0103",
        );
        let packets = ingest_payload(
            &state,
            &raw,
            FrameMeta {
                source_mac: "8c:1e:d9:03:09:b2".to_string(),
                capture_type: "beacon",
                rssi: Some(-42),
                channel: Some(6),
            },
            1_700_000_000.0,
        );
        assert_eq!(packets.len(), 1);
        let drones = state.drones.read();
        let entry = drones.get("1581FANLC258U029RTN6").expect("drone entry");
        assert_eq!(entry.src_mac, "8c:1e:d9:03:09:b2");
        assert_eq!(entry.rssi, Some(-42));
        assert_eq!(entry.last_ch, Some(6));
        assert_eq!(entry.pkt_count, 1);
        assert_eq!(entry.firmware_type, "new");
    }
}
