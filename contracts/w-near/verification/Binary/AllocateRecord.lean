import Binary.AllocateForward

/-! Actual689 zeroed/nonzero allocation dispatch and two-word result record. -/
namespace WNear.Binary.AllocateRecord
open Wasm Wasm.Near

def zeroed : Expr := [.local_get 3,.i32_eqz,.br_if 0,.local_get 1,.local_get 2,.call 313,.local_set 2,.br 1]
def ordinary : Expr := [.local_get 1,.local_get 2,.call 310,.local_set 2]
def guarded : Expr := [.local_get 1,.i32_eqz,.br_if 0,.block .empty zeroed]++ordinary
def record : Expr := [.local_get 0,.local_get 1,.store .i32 none {align:=2,offset:=4},
  .local_get 0,.local_get 2,.store .i32 none {align:=2,offset:=0}]
def body : Expr := [.block .empty guarded]++record
def function : Func := {type:=45,locals:=[],body,bodySize:=58}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32,.num .i32],results:=[]}

theorem module_function : wNearModule.funcs[641]?=some function := by kernel_rfl
theorem module_signature : wNearModule.types[45]?=some signature := by kernel_rfl
theorem activation (op : Nat) (out size alignment flag : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 size,.i32 alignment,.i32 flag])=10*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function]
end WNear.Binary.AllocateRecord
