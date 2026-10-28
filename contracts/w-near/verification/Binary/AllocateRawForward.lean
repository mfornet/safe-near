import Binary.Allocate

/-! Actual deployed allocation forwarding functions236 and310. -/
namespace WNear.Binary.AllocateRawForward
open Wasm Wasm.Near

def body236 : Expr := [.i32_const 1074896,.local_get 0,.local_get 1,.call 581]
def function236 : Func := {type:=13,locals:=[],body:=body236,bodySize:=18}
def body310 : Expr := [.local_get 0,.local_get 1,.call 236,.local_set 2,.local_get 2,.return]
def function310 : Func := {type:=13,locals:=[.num .i32],body:=body310,bodySize:=19}
def signature : FuncType := {params:=[.num .i32,.num .i32],results:=[.num .i32]}

theorem module236 : wNearModule.funcs[188]?=some function236 := by kernel_rfl
theorem module310 : wNearModule.funcs[262]?=some function310 := by kernel_rfl
theorem module_type : wNearModule.types[13]?=some signature := by kernel_rfl
theorem activation236 (op : Nat) (size alignment : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function236 [.i32 size,.i32 alignment])=9*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function236]
theorem activation310 (op : Nat) (size alignment : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function310 [.i32 size,.i32 alignment])=10*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function310,ValType.default]
end WNear.Binary.AllocateRawForward
