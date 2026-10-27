import Binary.AllocatePositive

/-! Actual f153 allocate-and-zero wrapper; only the positive direct-fit branch is selected below. -/
namespace WNear.Binary.AllocateZeroed
open Wasm Wasm.Near

def arguments : Expr := [.local_get 0,.local_get 1,.local_get 2]
def fill : Expr := [.local_tee 0,.i32_eqz,.br_if 0,.local_get 0,.i32_const 0,.local_get 1,.call 952,.drop]
def guarded : Expr := arguments++[.call 581]++fill
def body : Expr := [.block .empty guarded,.local_get 0]
def function : Func := {type:=15,locals:=[],body,bodySize:=37}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[.num .i32]}

theorem module_function : wNearModule.funcs[105]?=some function := by kernel_rfl
theorem module_signature : wNearModule.types[15]?=some signature := by kernel_rfl
theorem body_eq : f153.body=body := by kernel_rfl
theorem activation (op : Nat) (allocator size : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 allocator,.i32 size,.i32 1])=10*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function]
end WNear.Binary.AllocateZeroed
