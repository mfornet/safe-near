import Binary.AllocateZeroed

/-! Actual deployed allocation forwarding functions239 and313. -/
namespace WNear.Binary.AllocateForward
open Wasm Wasm.Near

def body239 : Expr := [.i32_const 1074896,.local_get 0,.local_get 1,.call 153]
def function239 : Func := {type:=13,locals:=[],body:=body239,bodySize:=18}
def body313 : Expr := [.local_get 0,.local_get 1,.call 239,.local_set 2,.local_get 2,.return]
def function313 : Func := {type:=13,locals:=[.num .i32],body:=body313,bodySize:=19}
def signature : FuncType := {params:=[.num .i32,.num .i32],results:=[.num .i32]}

theorem module239 : wNearModule.funcs[191]?=some function239 := by kernel_rfl
theorem module313 : wNearModule.funcs[265]?=some function313 := by kernel_rfl
theorem module_type : wNearModule.types[13]?=some signature := by kernel_rfl
theorem activation239 (op : Nat) (size alignment : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function239 [.i32 size,.i32 alignment])=9*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function239]
theorem activation313 (op : Nat) (size alignment : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function313 [.i32 size,.i32 alignment])=10*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function313,ValType.default]
end WNear.Binary.AllocateForward
