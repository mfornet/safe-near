import Binary.Valid.Context

/-! The bodies of code entries 0 to 74 (exclusive) validate. -/

namespace WNear.Binary

theorem valid_0_74 : RangeOk funcs_0_74 := by unfold RangeOk; kernel_rfl

end WNear.Binary
