import Binary.Bytes

/-! Code entries 0 to 73 of `contract.wasm`: functions `f48` to
`f121` as the decoder reads them, each with the kernel-checked theorem
`code_f<i>` that decoding its entry gives it (`#embed_wasm_code`). -/

namespace WNear.Binary

#embed_wasm_code wNearSource "../contract.wasm" 0 74

end WNear.Binary
