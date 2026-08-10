#![cfg_attr(not(target_os = "linux"), allow(dead_code))]

use std::{env, fmt::Write as _, io, time::Duration};

#[cfg(target_os = "linux")]
use std::{ffi::CString, io::Write, mem, time::Instant};

const ETH_P_ALL: u16 = 0x0003;

fn main() {
    if let Err(error) = run() {
        eprintln!("light-rid-capture: {error}");
        std::process::exit(1);
    }
}

fn run() -> io::Result<()> {
    let mut args = env::args().skip(1);
    let mut iface = String::new();
    let mut timeout_ms = 5_000_u64;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--interface" => iface = args.next().unwrap_or_default(),
            "--timeout-ms" => {
                timeout_ms = args
                    .next()
                    .and_then(|value| value.parse().ok())
                    .unwrap_or(timeout_ms);
            }
            "--help" | "-h" => {
                println!("Usage: light-rid-capture --interface IFACE [--timeout-ms N]");
                return Ok(());
            }
            _ => {}
        }
    }
    if iface.is_empty() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "--interface is required",
        ));
    }

    let duration = if timeout_ms == 0 {
        None
    } else {
        Some(Duration::from_millis(timeout_ms.max(250)))
    };
    capture(&iface, duration)
}

#[cfg(not(target_os = "linux"))]
fn capture(_iface: &str, _duration: Option<Duration>) -> io::Result<()> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "AF_PACKET capture is only available on Linux",
    ))
}

#[cfg(target_os = "linux")]
fn capture(iface: &str, duration: Option<Duration>) -> io::Result<()> {
    let fd = open_packet_socket(iface)?;
    let result = receive_loop(fd, duration);
    unsafe { libc::close(fd) };
    result
}

#[cfg(target_os = "linux")]
fn open_packet_socket(iface: &str) -> io::Result<i32> {
    let fd = unsafe { libc::socket(libc::AF_PACKET, libc::SOCK_RAW, ETH_P_ALL.to_be() as i32) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let name = CString::new(iface)
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "invalid interface name"))?;
    let index = unsafe { libc::if_nametoindex(name.as_ptr()) };
    if index == 0 {
        let error = io::Error::last_os_error();
        unsafe { libc::close(fd) };
        return Err(error);
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
    // Match libpcap/tcpdump's capture semantics.  Some mac80211 drivers only
    // deliver every monitor-mode management frame to packet sockets that have
    // explicitly joined promiscuous membership, even though ordinary beacons
    // remain visible without it.
    let membership = libc::packet_mreq {
        mr_ifindex: index as i32,
        mr_type: libc::PACKET_MR_PROMISC as u16,
        mr_alen: 0,
        mr_address: [0; 8],
    };
    let rc = unsafe {
        libc::setsockopt(
            fd,
            libc::SOL_PACKET,
            libc::PACKET_ADD_MEMBERSHIP,
            (&raw const membership).cast::<libc::c_void>(),
            mem::size_of::<libc::packet_mreq>() as libc::socklen_t,
        )
    };
    if rc != 0 {
        let error = io::Error::last_os_error();
        unsafe { libc::close(fd) };
        return Err(error);
    }
    // The router has little CPU headroom while Python renders snapshots.  A
    // larger kernel queue prevents short parser stalls from dropping a burst
    // of RID beacons before userspace can read them.
    let receive_buffer: libc::c_int = 1_048_576;
    let rc = unsafe {
        libc::setsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_RCVBUF,
            (&raw const receive_buffer).cast::<libc::c_void>(),
            mem::size_of_val(&receive_buffer) as libc::socklen_t,
        )
    };
    if rc != 0 {
        let error = io::Error::last_os_error();
        unsafe { libc::close(fd) };
        return Err(error);
    }
    let timeout = libc::timeval {
        tv_sec: 0,
        tv_usec: 250_000,
    };
    let rc = unsafe {
        libc::setsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_RCVTIMEO,
            (&raw const timeout).cast::<libc::c_void>(),
            mem::size_of::<libc::timeval>() as libc::socklen_t,
        )
    };
    if rc != 0 {
        let error = io::Error::last_os_error();
        unsafe { libc::close(fd) };
        return Err(error);
    }
    Ok(fd)
}

#[cfg(target_os = "linux")]
fn receive_loop(fd: i32, duration: Option<Duration>) -> io::Result<()> {
    let deadline = duration.map(|value| Instant::now() + value);
    let mut buffer = vec![0_u8; 8192];
    let stdout = io::stdout();
    let mut output = stdout.lock();
    while deadline.map(|value| Instant::now() < value).unwrap_or(true) {
        let size = unsafe {
            libc::recv(
                fd,
                buffer.as_mut_ptr().cast::<libc::c_void>(),
                buffer.len(),
                0,
            )
        };
        if size < 0 {
            let error = io::Error::last_os_error();
            if matches!(
                error.kind(),
                io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
            ) {
                continue;
            }
            return Err(error);
        }
        if let Some(line) = decode_record(&buffer[..size as usize]) {
            output.write_all(line.as_bytes())?;
            output.write_all(b"\n")?;
            output.flush()?;
        }
    }
    Ok(())
}

fn decode_record(raw: &[u8]) -> Option<String> {
    let (offset, rssi, channel) = parse_radiotap(raw).unwrap_or((0, None, None));
    let dot11 = raw.get(offset..)?;
    if dot11.len() < 24 {
        return None;
    }
    let control = u16::from_le_bytes([dot11[0], dot11[1]]);
    if ((control >> 2) & 0x3) != 0 {
        return None;
    }
    let subtype = ((control >> 4) & 0xf) as u8;
    if !matches!(subtype, 5 | 8 | 13) {
        return None;
    }
    let mac = &dot11[10..16];
    let ssid = extract_ssid(dot11, subtype).unwrap_or_default();
    let rid_candidate =
        ssid.starts_with(b"RID-") || dot11.windows(3).any(|window| window == [0xfa, 0x0b, 0xbc]);
    // Probe responses and public/vendor action traffic are extremely noisy on
    // the AR750S.  Python only uses these subtypes when they contain an RID
    // payload, so discard unrelated frames here while retaining every beacon
    // for the AP list.  This keeps RID records from waiting behind Apple/NAN
    // action bursts in the stdout pipe on the 560 MHz MIPS CPU.
    if subtype != 8 && !rid_candidate {
        return None;
    }
    let mut line = format!(
        "RIDCAP1\t{subtype}\t{:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}\t{}\t{}\t",
        mac[0],
        mac[1],
        mac[2],
        mac[3],
        mac[4],
        mac[5],
        rssi.map(|value| value.to_string()).unwrap_or_default(),
        channel.map(|value| value.to_string()).unwrap_or_default(),
    );
    append_hex(&mut line, &ssid);
    line.push('\t');
    append_hex(&mut line, dot11);
    Some(line)
}

fn extract_ssid(dot11: &[u8], subtype: u8) -> Option<Vec<u8>> {
    let mut cursor = match subtype {
        5 | 8 => 36,
        _ => return None,
    };
    while cursor + 2 <= dot11.len() {
        let id = dot11[cursor];
        let length = dot11[cursor + 1] as usize;
        cursor += 2;
        let value = dot11.get(cursor..cursor + length)?;
        if id == 0 {
            return Some(value.to_vec());
        }
        cursor += length;
    }
    None
}

fn append_hex(output: &mut String, bytes: &[u8]) {
    for byte in bytes {
        let _ = write!(output, "{byte:02x}");
    }
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
    let mut present_offset = 4_usize;
    while read_u32(raw, present_offset)? & (1 << 31) != 0 {
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
            channel = frequency_to_channel(u16::from_le_bytes([field[0], field[1]]));
        } else if index == 5 {
            rssi = Some(i8::from_ne_bytes([field[0]]) as i32);
        }
        cursor += size;
    }
    Some((header_len, rssi, channel))
}

fn read_u32(raw: &[u8], offset: usize) -> Option<u32> {
    Some(u32::from_le_bytes(
        raw.get(offset..offset + 4)?.try_into().ok()?,
    ))
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
    fn emits_beacon_record_with_metadata() {
        let mut frame = vec![0, 0, 14, 0, 0x28, 0, 0, 0, 0x85, 0x09, 0, 0, 0xd6, 0];
        frame.extend([0x80, 0x00, 0, 0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);
        frame.extend([0x8c, 0x1e, 0xd9, 0x03, 0x09, 0xb2]);
        frame.extend([0; 8]);
        frame.extend([0; 12]);
        frame.extend([0, 3, b'R', b'I', b'D']);
        let line = decode_record(&frame).expect("beacon record");
        assert!(line.starts_with("RIDCAP1\t8\t8c:1e:d9:03:09:b2\t-42\t6\t524944\t"));
    }

    #[test]
    fn rejects_data_frame() {
        let mut frame = vec![0, 0, 8, 0, 0, 0, 0, 0];
        frame.extend([0x08, 0x00]);
        frame.extend([0; 22]);
        assert!(decode_record(&frame).is_none());
    }

    #[test]
    fn decodes_router_radiotap_with_extended_presence_words() {
        let raw = hex_bytes(
            "000026002f4000a0200800a020080000afd25e265d000000100c8509c000e0000000ca00e001\
             80000000ffffffffffff8c1ed9f577968c1ed9f577960000e8acb52d00000000a00021040018\
             5249442d3135383146414e4c433235385530323952544e36dd53fa0bbc0decff2048fffffe31\
             35383146414e4c433235385530323952544e3630303030303030300001013f693b483403ec11\
             d007ffffffffffffffffffff00000000000000c60901000000000000000000000023582546",
        );
        let line = decode_record(&raw).expect("RID beacon from GL-AR750S capture");
        assert!(line.starts_with("RIDCAP1\t8\t8c:1e:d9:f5:77:96\t"));
        assert!(line.contains("\t6\t5249442d3135383146414e4c433235385530323952544e36\t"));
        assert!(line.contains("fa0bbc0decff2048fffffe"));
    }

    #[test]
    fn drops_unrelated_action_frames_before_python_pipe() {
        let mut frame = vec![0, 0, 8, 0, 0, 0, 0, 0];
        frame.extend([0xd0, 0x00, 0, 0]);
        frame.extend([0xff; 6]);
        frame.extend([0x10, 0x20, 0x30, 0x40, 0x50, 0x60]);
        frame.extend([0; 8]);
        frame.extend([0x7f, 0x00, 0x17, 0xf2, 0x08]);
        assert!(decode_record(&frame).is_none());
    }

    fn hex_bytes(text: &str) -> Vec<u8> {
        let compact: String = text.chars().filter(|ch| !ch.is_whitespace()).collect();
        compact
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| {
                u8::from_str_radix(std::str::from_utf8(pair).expect("hex pair"), 16)
                    .expect("hex byte")
            })
            .collect()
    }
}
