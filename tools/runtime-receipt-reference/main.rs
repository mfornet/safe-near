use std::io::{self, Read};
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;
    let result = node_runtime::safe_near_receipt_reference::execute(serde_json::from_str(&input)?)?;
    println!("{}", serde_json::to_string(&result)?);
    Ok(())
}
