use std::{env, fs, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=../station_edition/light_rid/web_server.py");
    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR"));
    let source_path = PathBuf::from("../station_edition/light_rid/web_server.py");
    let source = fs::read_to_string(&source_path).unwrap_or_else(|_| {
        "<!doctype html><html lang=\"zh\"><head><meta charset=\"utf-8\"><title>Light RID Scanner</title></head><body><h1>Light RID Scanner</h1></body></html>".to_string()
    });
    let page = extract_triple_string(&source, "_PAGE_HTML").unwrap_or_else(|| {
        "<!doctype html><html lang=\"zh\"><head><meta charset=\"utf-8\"><title>Light RID Scanner</title></head><body><h1>Light RID Scanner</h1></body></html>".to_string()
    });
    fs::write(out_dir.join("station_page.html"), page).expect("write station page");
}

fn extract_triple_string(source: &str, name: &str) -> Option<String> {
    let start_marker = format!("{name} = \"\"\"");
    let start = source.find(&start_marker)? + start_marker.len();
    let rest = &source[start..];
    let end = rest.find("\"\"\"")?;
    Some(rest[..end].to_string())
}
