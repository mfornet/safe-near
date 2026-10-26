import Binary.Bytes

/-! Code entries 255 to 290 of `contract.wasm`: functions `f303` to
`f338` as the decoder reads them, each with the kernel-checked theorem
`code_f<i>` that decoding its entry gives it (`#embed_wasm_code`). -/

namespace WNear.Binary

#embed_wasm_code wNearSource "../contract.wasm" 255 291

end WNear.Binary
