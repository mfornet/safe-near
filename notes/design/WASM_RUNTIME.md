# WASM Runtime

> There is partial work that we can use here: https://github.com/cajal-technologies/talos)

WASM Runtime is responsible to running arbitrary WASM code over some custom
defined host. 

We can build trust in our implementation about the WASM Runtime by running
official and custom made wasm testsuite. There is a comprehensive wasm
testsuite, and we can extract all history of NEAR blockchain into a
testsuite and compare that our Runtime (+Host) produce the same outcome
as the official one.

Interface: This implementation should have the same ability as any other
wasm runtime such as wasmtime or wasmer and should allow for a plug&play
replacement in most scenarios, even if sometime is not feasible since
out implementation doesn't need to be as performant as others. This should
allows us to run as many fuzz tests as possible.
