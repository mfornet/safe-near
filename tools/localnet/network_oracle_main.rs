// Build-only adapter: the entry point of the network oracle.  The oracle itself is the module
// `safe_near_oracle` that `build.py` adds to the `near-network` crate (see `network_oracle.rs`).
fn main() {
    near_network::safe_near_oracle::main();
}
