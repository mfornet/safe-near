// Child module of pinned verifier.rs: calls its actual private nonce validator.
use super::*;
use serde_json::{Value, json};

pub fn execute(v: Value) -> Result<Value, Box<dyn std::error::Error>> {
    let number = |key: &str| -> Result<u64, Box<dyn std::error::Error>> {
        Ok(v[key].as_u64().ok_or("missing u64")?)
    };
    let version: u32 = number("protocolVersion")?.try_into()?;
    if !(84..=86).contains(&version) {
        return Err("nonce reference supports versions 84 through 86".into());
    }
    let mode = match v["nonceMode"].as_str() {
        Some("monotonic") => NonceMode::Monotonic,
        Some("strict") => NonceMode::Strict,
        _ => return Err("unknown nonce mode".into()),
    };
    let nonce = number("nonce")?;
    let current = number("currentNonce")?;
    let height = if v["blockHeight"].is_null() {
        None
    } else {
        Some(number("blockHeight")?)
    };
    // This gate belongs to ValidatedTransaction::new, before account admission.
    if mode == NonceMode::Strict
        && !near_primitives::version::ProtocolFeature::StrictNonce.enabled(version)
    {
        return Ok(json!({"error":"invalidTransactionVersion"}));
    }
    match verify_nonce(nonce, current, height, mode) {
        Ok(()) => Ok(json!({"error":null})),
        Err(InvalidTxError::InvalidNonce { tx_nonce, ak_nonce }) => {
            Ok(json!({"error":"invalidNonce", "nonce":tx_nonce, "currentNonce":ak_nonce}))
        }
        Err(InvalidTxError::NonceTooLarge {
            tx_nonce,
            upper_bound,
        }) => Ok(json!({"error":"nonceTooLarge", "nonce":tx_nonce, "upperBound":upper_bound})),
        Err(error) => Err(format!("unexpected nonce error: {error:?}").into()),
    }
}
