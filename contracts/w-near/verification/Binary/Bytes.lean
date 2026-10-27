import WasmEmbed.Embed

/-!
# The bytes of `contract.wasm`

`wNearSource` holds the bytes of the deployed binary, read from
`../contract.wasm` when this file is elaborated, in the chunked form the
kernel reads quickly (`Wasm.ByteSource`). `wNearBytes` is the byte array it
holds; the runtime adapter tests check that it is the file.
-/

namespace WNear.Binary

-- The literal is a tree of depth 12; elaborating it needs more than the default depth.
set_option maxRecDepth 100000 in
/-- `contract.wasm`, as deployed, as a byte source. -/
def wNearSource : Wasm.ByteSource := byte_source% "../contract.wasm"

/-- `contract.wasm`, as deployed. -/
def wNearBytes : ByteArray := wNearSource.toBytes

end WNear.Binary
