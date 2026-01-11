//! Integration tests against real Steam VDF files.

use std::path::Path;
use steam_vdf_parser::{parse_binary, parse_text};

#[test]
fn test_parse_real_localconfig_text() {
    let path = Path::new("tests/fixtures/localconfig.vdf");
    let content = std::fs::read_to_string(path).expect("Failed to read localconfig.vdf");

    let result = parse_text(&content);
    assert!(
        result.is_ok(),
        "Failed to parse localconfig.vdf: {:?}",
        result.err()
    );

    let vdf = result.unwrap();
    assert_eq!(vdf.key, "UserLocalConfigStore");

    let obj = vdf.as_obj().expect("Root should be an object");
    assert!(!obj.is_empty(), "Root should have keys");

    // Check for known keys that should exist in localconfig
    assert!(obj.get("Broadcast").is_some());
    assert!(obj.get("friends").is_some());
}

#[test]
fn test_parse_real_appinfo_binary() {
    let path = Path::new("tests/fixtures/appinfo.vdf");
    let data = std::fs::read(path).expect("Failed to read appinfo.vdf");

    let result = parse_binary(&data);
    assert!(
        result.is_ok(),
        "Failed to parse appinfo.vdf: {:?}",
        result.err()
    );

    let vdf = result.unwrap();
    assert!(vdf.key.starts_with("appinfo_universe_"));

    let obj = vdf.as_obj().expect("Root should be an object");
    assert!(!obj.is_empty(), "Root should have keys");

    // appinfo.vdf should contain apps (numeric keys as strings)
    // Check that we have at least some entries
    assert!(obj.len() > 100, "Should have many apps in appinfo.vdf");
}
