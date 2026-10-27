import Binary.StorePair
import Wasm.ValidateCertificate

/-! A bounded first certificate for the actual deployed f566 body. This checks
its six instructions independently of all other function bodies. It does not
assert whole-module validation. -/
namespace WNear.Binary.ValidationStorePair
open Wasm

/-- f566 only needs its three argument locals and one memory; the other
validation-context fields and the memory limits are arbitrary. -/
theorem body_ok (ctx : Validate.Context) (memory : MemType) :
    Validate.body
      {ctx with mems := #[memory], locals := #[.num .i32, .num .i64, .num .i64], «return» := some []}
      [] StorePair.body = .ok () := by
  rfl

/-- The actual final-loop function checker accepts this deployed function.
This is a local body certificate, to be assembled with the static context. -/
theorem checkFunction_ok (ctx : Validate.Context) (memory : MemType) :
    Validate.Certificate.checkFunction ctx.features wNearModule
      {ctx with mems := #[memory]} StorePair.function = .ok () := by
  rfl

end WNear.Binary.ValidationStorePair
