//! Offline entry point: no archive, network client or synthetic genesis involved.
use std::io::Read;
fn main() {
    if std::env::args().nth(1).as_deref() == Some("--metadata") {
        println!(
            "{}",
            serde_json::json!({"format":node_runtime::historical_capture::FORMAT,
            "sourceRevision":node_runtime::historical_capture::REVISION,
            "adapterSha256":env!("SAFE_NEAR_HISTORY_ADAPTER_SHA256")})
        );
        return;
    }
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).unwrap();
    let input: serde_json::Value = serde_json::from_str(&input).expect("invalid witness JSON");
    let request = input.get("request").unwrap_or(&input);
    let result = node_runtime::historical_capture::replay(request);
    assert_eq!(
        result, request["nativeExpected"],
        "offline result differs from captured native result"
    );
    if let Some(archive) = input.get("archive") {
        node_runtime::historical_capture::verify_archive(request, archive, &result);
        println!(
            "{}",
            serde_json::json!({"archiveVerified":true,"observations":result})
        );
    } else {
        println!("{}", result);
    }
}
