use std::io::{self, Read};
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;
    println!(
        "{}",
        node_runtime::safe_near_finance_reference::execute(serde_json::from_str(&input)?)?
    );
    Ok(())
}
