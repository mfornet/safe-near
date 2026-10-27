import Binary.AllocateSearch

/-! Exact deployed580 activation metadata. -/
namespace WNear.Binary.AllocateSearch
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 30000

theorem function_locals : Allocate.searchFunction.locals = List.replicate 9 (.num .i32) := by kernel_rfl
theorem function_type : Allocate.searchFunction.type = 34 := by kernel_rfl
theorem module_function : wNearModule.funcs[532]? = some Allocate.searchFunction := by kernel_rfl

theorem activation (op : Nat) (words root context vtable : UInt32) :
    activationGas op (wasmLocals Allocate.searchFunction [.i32 words,.i32 1,.i32 root,.i32 context,.i32 vtable])=15*op := by
  simp [wasmLocals,function_locals,activationGas,ValType.default,List.replicate_succ]
end WNear.Binary.AllocateSearch
