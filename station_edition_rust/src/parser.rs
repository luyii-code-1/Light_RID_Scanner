use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

const ODID_MSG_SIZE: usize = 25;
const MSG_TYPE_BASIC_ID: u8 = 0x0;
const MSG_TYPE_LOCATION: u8 = 0x1;
const MSG_TYPE_SYSTEM: u8 = 0x4;
const MSG_TYPE_PACK: u8 = 0xF;
const DJI_PREFIX: &[u8] = &[0xfa, 0x0b, 0xbc, 0x0d];
const GB_MARKER: &[u8] = &[0xff, 0x20, 0x48, 0xff, 0xff, 0xfe];

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct TrackSample {
    pub track_type: String,
    pub sample_type: String,
    pub sn: String,
    pub lat: f64,
    pub lon: f64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub alt: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub timestamp_ms: Option<i64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub receive_time_ms: Option<i64>,
    pub source: String,
    pub coordinate_system: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ParseResult {
    pub ok: bool,
    pub format: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sub_format: Option<String>,
    #[serde(default)]
    pub sn: String,
    #[serde(default)]
    pub uas_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub aircraft_position: Option<Value>,
    #[serde(default)]
    pub operator_positions: Vec<Value>,
    #[serde(default)]
    pub track_samples: Vec<TrackSample>,
    #[serde(default)]
    pub decoded: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}

pub fn normalize_parse_mode(mode: Option<&str>) -> &'static str {
    match mode
        .unwrap_or("auto")
        .trim()
        .to_ascii_lowercase()
        .replace('-', "_")
        .as_str()
    {
        "" | "default" | "auto" => "auto",
        "gb" | "gb46750" | "dji_gb46750" | "gb46750_2025" => "gb46750_2025",
        "old" | "legacy" | "odid" | "odid_legacy" | "dji_old" | "dji_old_odid" => "dji_old_odid",
        _ => "auto",
    }
}

pub fn raw_packet_string_to_bytes(input: &str) -> Vec<u8> {
    let mut text = input.trim().to_string();
    if let Some((head, _)) = text.split_once("...") {
        text = head.to_string();
    }
    if text.to_ascii_lowercase().starts_with("hex:") {
        text = text[4..].to_string();
    }
    text = text.replace("\\x", " ").replace("0x", " ");
    let mut hex_text: String = text.chars().filter(|c| c.is_ascii_hexdigit()).collect();
    if hex_text.len() % 2 == 1 {
        hex_text.pop();
    }
    hex::decode(hex_text).unwrap_or_default()
}

pub fn parse_raw_packet_string(input: &str, mode: Option<&str>) -> ParseResult {
    parse_rid_payload(&raw_packet_string_to_bytes(input), mode)
}

pub fn parse_rid_payload(data: &[u8], mode: Option<&str>) -> ParseResult {
    let mode = normalize_parse_mode(mode);
    if matches!(mode, "auto" | "gb46750_2025") {
        if let Some(result) = parse_gb46750_2025(data) {
            return result;
        }
        if mode == "gb46750_2025" {
            return unknown("GB46750_2025 payload not found");
        }
    }
    if matches!(mode, "auto" | "dji_old_odid") {
        if has_gb_blocking_marker(data) && mode == "auto" {
            return unknown("GB46750 marker present without valid packet");
        }
        if let Some(result) = parse_legacy_odid(data) {
            return result;
        }
    }
    unknown("RID payload not recognized")
}

pub fn parse_rid_payloads(data: &[u8], mode: Option<&str>) -> Value {
    let mut packets = Vec::new();
    if let Some(gb) = parse_gb46750_2025(data) {
        packets.push(json!(gb));
    }
    for payload in legacy_candidates(data) {
        if let Some(old) = parse_legacy_odid(&payload) {
            packets.push(json!(old));
        }
    }
    if packets.is_empty() {
        let single = parse_rid_payload(data, mode);
        if single.ok {
            packets.push(json!(single));
        }
    }
    let mut tracks = serde_json::Map::new();
    let mut samples = Vec::new();
    for packet in &packets {
        let sn = packet
            .get("sn")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string();
        for sample in packet
            .get("track_samples")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            samples.push(sample.clone());
            let entry = tracks
                .entry(sn.clone())
                .or_insert_with(|| json!({"aircraft":[],"operator":[]}));
            if let Some(kind) = sample.get("track_type").and_then(Value::as_str)
                && let Some(arr) = entry.get_mut(kind).and_then(Value::as_array_mut)
            {
                arr.push(sample.clone());
            }
        }
    }
    json!({
        "ok": !packets.is_empty(),
        "count": packets.len(),
        "packets": packets,
        "track_samples": samples,
        "tracks": tracks,
    })
}

fn parse_gb46750_2025(data: &[u8]) -> Option<ParseResult> {
    let starts = find_prefixes(data, DJI_PREFIX);
    for start in starts {
        let vendor = &data[start..];
        if vendor.len() < 68 {
            continue;
        }
        if vendor.get(5..11) == Some(GB_MARKER) && vendor.len() >= 60 {
            let sn = ascii_text(&vendor[11..31], 4, 20)?;
            let uas_id = ascii_text(&vendor[31..39], 0, 20).unwrap_or_default();
            let pilot_lon = le_i32(vendor, 42)? as f64 * 1e-7;
            let pilot_lat = le_i32(vendor, 46)? as f64 * 1e-7;
            let drone_lon = le_i32(vendor, 52)? as f64 * 1e-7;
            let drone_lat = le_i32(vendor, 56)? as f64 * 1e-7;
            if !coord_pair_valid(drone_lat, drone_lon) || !coord_pair_valid(pilot_lat, pilot_lon) {
                continue;
            }
            return Some(gb_result(
                sn,
                uas_id,
                drone_lat,
                drone_lon,
                pilot_lat,
                pilot_lon,
                "GB46750_STANDARD_PACKET",
            ));
        }
        if vendor.len() >= 72 {
            let sn = ascii_text(&vendor[11..31], 4, 20)?;
            let uas_id = ascii_text(&vendor[31..39], 0, 20).unwrap_or_default();
            let pilot_lon = le_i32(vendor, 42)? as f64 * 1e-7;
            let pilot_lat = le_i32(vendor, 46)? as f64 * 1e-7;
            let drone_lon = le_i32(vendor, 52)? as f64 * 1e-7;
            let drone_lat = le_i32(vendor, 56)? as f64 * 1e-7;
            if coord_pair_valid(drone_lat, drone_lon) && coord_pair_valid(pilot_lat, pilot_lon) {
                return Some(gb_result(
                    sn,
                    uas_id,
                    drone_lat,
                    drone_lon,
                    pilot_lat,
                    pilot_lon,
                    "GB46750_STANDARD_PACKET",
                ));
            }
        }
    }
    None
}

fn parse_legacy_odid(data: &[u8]) -> Option<ParseResult> {
    let mut basic_sn = String::new();
    let mut aircraft: Option<Value> = None;
    let mut operator: Option<Value> = None;
    for payload in legacy_candidates(data) {
        let mt = (payload[0] >> 4) & 0x0f;
        match mt {
            MSG_TYPE_BASIC_ID => {
                if let Some(sn) = decode_basic_id(&payload) {
                    basic_sn = sn;
                }
            }
            MSG_TYPE_LOCATION => {
                aircraft = decode_location(&payload);
            }
            MSG_TYPE_SYSTEM => {
                operator = decode_system(&payload);
            }
            MSG_TYPE_PACK => {}
            _ => {}
        }
    }
    if basic_sn.is_empty() || aircraft.is_none() {
        return None;
    }
    let aircraft_position = aircraft?;
    let mut operator_positions = Vec::new();
    if let Some(op) = operator {
        operator_positions.push(op);
    }
    let decoded = decoded_value(
        &basic_sn,
        &aircraft_position,
        operator_positions.first(),
        "DJI_OLD_ODID",
    );
    Some(ParseResult {
        ok: true,
        format: "DJI_OLD_ODID".to_string(),
        sub_format: None,
        sn: basic_sn.clone(),
        uas_id: basic_sn.clone(),
        aircraft_position: Some(aircraft_position.clone()),
        operator_positions: operator_positions.clone(),
        track_samples: samples(&basic_sn, &aircraft_position, operator_positions.first()),
        decoded,
        error: None,
    })
}

fn gb_result(
    sn: String,
    uas_id: String,
    drone_lat: f64,
    drone_lon: f64,
    pilot_lat: f64,
    pilot_lon: f64,
    sub: &str,
) -> ParseResult {
    let aircraft = json!({"role":"aircraft","source":"GB46750_LOCATION","lat":drone_lat,"lon":drone_lon,"coordinate_system":"WGS84"});
    let operator = json!({"role":"operator","source":"GB46750_OPERATOR","lat":pilot_lat,"lon":pilot_lon,"coordinate_system":"WGS84"});
    let decoded = decoded_value(&sn, &aircraft, Some(&operator), "GB46750_2025");
    ParseResult {
        ok: true,
        format: "GB46750_2025".to_string(),
        sub_format: Some(sub.to_string()),
        sn: sn.clone(),
        uas_id,
        aircraft_position: Some(aircraft.clone()),
        operator_positions: vec![operator.clone()],
        track_samples: samples(&sn, &aircraft, Some(&operator)),
        decoded,
        error: None,
    }
}

fn decoded_value(sn: &str, aircraft: &Value, operator: Option<&Value>, format: &str) -> Value {
    json!({
        "basic_id": {"uas_id": sn, "id_type": "Serial"},
        "location": {"lat": aircraft["lat"], "lon": aircraft["lon"], "alt_geodetic": aircraft.get("alt").cloned().unwrap_or(Value::Null)},
        "system": operator.map(|op| json!({"pilot_lat": op["lat"], "pilot_lon": op["lon"], "pilot_loc_type_text": op.get("source").cloned().unwrap_or(Value::Null)})).unwrap_or(Value::Null),
        "metadata": {"format": format, "rid_format": format, "aircraft_position": aircraft, "operator_positions": operator.into_iter().cloned().collect::<Vec<_>>()},
    })
}

fn samples(sn: &str, aircraft: &Value, operator: Option<&Value>) -> Vec<TrackSample> {
    let mut out = vec![sample(sn, "aircraft", aircraft)];
    if let Some(op) = operator {
        out.push(sample(sn, "operator", op));
    }
    out
}

fn sample(sn: &str, kind: &str, src: &Value) -> TrackSample {
    TrackSample {
        track_type: kind.to_string(),
        sample_type: kind.to_string(),
        sn: sn.to_string(),
        lat: src["lat"].as_f64().unwrap_or_default(),
        lon: src["lon"].as_f64().unwrap_or_default(),
        alt: src.get("alt").and_then(Value::as_f64),
        timestamp_ms: None,
        receive_time_ms: None,
        source: src
            .get("source")
            .and_then(Value::as_str)
            .unwrap_or("RID")
            .to_string(),
        coordinate_system: "WGS84".to_string(),
    }
}

fn legacy_candidates(data: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    for i in 0..data.len().saturating_sub(ODID_MSG_SIZE - 1) {
        let b = data[i];
        let mt = (b >> 4) & 0x0f;
        let version = b & 0x0f;
        if matches!(
            mt,
            MSG_TYPE_BASIC_ID | MSG_TYPE_LOCATION | MSG_TYPE_SYSTEM | MSG_TYPE_PACK
        ) && version <= 2
        {
            out.push(data[i..i + ODID_MSG_SIZE].to_vec());
        }
    }
    out
}

fn decode_basic_id(msg: &[u8]) -> Option<String> {
    if ((msg[0] >> 4) & 0x0f) != MSG_TYPE_BASIC_ID {
        return None;
    }
    ascii_text(&msg[2..22], 4, 20)
}

fn decode_location(msg: &[u8]) -> Option<Value> {
    if ((msg[0] >> 4) & 0x0f) != MSG_TYPE_LOCATION {
        return None;
    }
    let lat = le_i32(msg, 5)? as f64 * 1e-7;
    let lon = le_i32(msg, 9)? as f64 * 1e-7;
    if !coord_pair_valid(lat, lon) {
        return None;
    }
    let alt_raw = u16::from_le_bytes([msg[15], msg[16]]);
    let alt = alt_raw as f64 * 0.5 - 1000.0;
    Some(
        json!({"role":"aircraft","source":"ODID_LOCATION","lat":lat,"lon":lon,"alt":alt,"coordinate_system":"WGS84"}),
    )
}

fn decode_system(msg: &[u8]) -> Option<Value> {
    if ((msg[0] >> 4) & 0x0f) != MSG_TYPE_SYSTEM {
        return None;
    }
    let lat = le_i32(msg, 15)? as f64 * 1e-7;
    let lon = le_i32(msg, 19)? as f64 * 1e-7;
    if !coord_pair_valid(lat, lon) {
        return None;
    }
    Some(
        json!({"role":"operator","source":"ODID_SYSTEM","lat":lat,"lon":lon,"coordinate_system":"WGS84"}),
    )
}

fn ascii_text(raw: &[u8], min_len: usize, max_len: usize) -> Option<String> {
    let text = raw
        .iter()
        .copied()
        .take_while(|b| *b != 0)
        .filter(|b| (32..=126).contains(b))
        .map(char::from)
        .collect::<String>()
        .trim()
        .to_string();
    if text.len() < min_len
        || text.len() > max_len
        || !text.chars().all(|c| c.is_ascii_alphanumeric())
    {
        None
    } else {
        Some(text)
    }
}

fn coord_pair_valid(lat: f64, lon: f64) -> bool {
    (-90.0..=90.0).contains(&lat)
        && (-180.0..=180.0).contains(&lon)
        && !(lat.abs() < 5.0 && lon.abs() < 5.0)
}

fn le_i32(data: &[u8], off: usize) -> Option<i32> {
    data.get(off..off + 4)
        .map(|v| i32::from_le_bytes([v[0], v[1], v[2], v[3]]))
}

fn find_prefixes(data: &[u8], needle: &[u8]) -> Vec<usize> {
    data.windows(needle.len())
        .enumerate()
        .filter_map(|(idx, w)| (w == needle).then_some(idx))
        .collect()
}

fn has_gb_blocking_marker(data: &[u8]) -> bool {
    data.windows(GB_MARKER.len()).any(|w| w == GB_MARKER)
}

fn unknown(error: &str) -> ParseResult {
    ParseResult {
        ok: false,
        format: "UNKNOWN".to_string(),
        sub_format: None,
        sn: String::new(),
        uas_id: String::new(),
        aircraft_position: None,
        operator_positions: Vec::new(),
        track_samples: Vec::new(),
        decoded: Value::Null,
        error: Some(error.to_string()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEGACY_ODID_RAW: &str = "00 00 12 00 2e 48 00 00 00 0c 85 09 c0 00 b4 01 00 00 80 00 00 00 ff ff ff ff ff ff 8c 1e d9 03 09 b2 8c 1e d9 03 09 b2 00 00 e8 0c 6b 22 00 00 00 00 a0 00 21 04 00 18 52 49 44 2d 31 35 38 31 46 38 44 42 57 32 35 42 38 30 30 42 33 34 31 37 dd 53 fa 0b bc 0d 06 f1 19 03 01 12 31 35 38 31 46 38 44 42 57 32 35 42 38 30 30 42 33 34 31 37 00 00 00 11 20 ac 16 00 a3 d4 ea 11 cb fe 3c 48 e2 08 9e 08 79 08 2c 04 c6 25 0a 00 41 09 ff ee ea 11 99 b7 3d 48 01 00 00 00 00 00 00 02 00 08 d7 74 da 0d 00";
    const GB46750_STANDARD_SAMPLE: &str = "fa0bbc0d24ff2048fffffe3135383146414e4c433235385530323952544e363030303030303030000101d1823b483bf2eb11ed0769833b4822f0eb1105001c00284700c2083d0902000c050478acc5529e0103";

    #[test]
    fn parses_gb46750_standard_roles() {
        let data = raw_packet_string_to_bytes(GB46750_STANDARD_SAMPLE);
        let result = parse_rid_payload(&data, Some("gb46750_2025"));
        assert!(result.ok, "{result:?}");
        assert_eq!(result.format, "GB46750_2025");
        assert_eq!(result.sn, "1581FANLC258U029RTN6");
        assert_eq!(result.uas_id, "00000000");
        assert_eq!(
            result
                .track_samples
                .iter()
                .map(|s| s.track_type.as_str())
                .collect::<Vec<_>>(),
            vec!["aircraft", "operator"]
        );
    }

    #[test]
    fn legacy_invalid_basic_id_is_rejected() {
        let mut payload = vec![0u8; 25];
        payload[0] = 0x00;
        payload[1] = 0x01;
        payload[2..6].copy_from_slice(b".HP:");
        let result = parse_rid_payload(&payload, Some("dji_old_odid"));
        assert!(!result.ok);
        assert_eq!(result.format, "UNKNOWN");
    }

    #[test]
    fn multi_parser_accumulates_packets() {
        let mut data = raw_packet_string_to_bytes(LEGACY_ODID_RAW);
        data.extend(raw_packet_string_to_bytes(GB46750_STANDARD_SAMPLE));
        let result = parse_rid_payloads(&data, Some("auto"));
        assert!(result["ok"].as_bool().unwrap());
        assert!(result["count"].as_u64().unwrap() >= 1);
        assert!(result["track_samples"].as_array().unwrap().len() >= 2);
    }
}
