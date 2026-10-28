import Binary.AllocateForward

/-! The actual690 stack-record forwarding function. -/
namespace WNear.Binary.AllocateRecordCopy
open Wasm Wasm.Near

def reserve : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 3,.global_set 0]
def arguments : Expr := [.local_get 3,.i32_const 8,.i32_binop .add,.local_get 1,.local_get 2,.i32_const 1]
def copy : Expr := [.local_get 0,.local_get 3,.load .i32 none {align:=2,offset:=8},.store .i32 none {align:=2,offset:=0},
  .local_get 0,.local_get 3,.load .i32 none {align:=2,offset:=12},.store .i32 none {align:=2,offset:=4}]
def restore : Expr := [.local_get 3,.i32_const 16,.i32_binop .add,.global_set 0]
def body : Expr := reserve ++ arguments ++ [.call 689] ++ copy ++ restore
def function : Func := {type:=31,locals:=[.num .i32],body,bodySize:=69}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[]}
theorem module_function : wNearModule.funcs[642]?=some function := by kernel_rfl
theorem module_type : wNearModule.types[31]?=some signature := by kernel_rfl
theorem activation (op : Nat) (out size alignment : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 size,.i32 alignment])=10*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.AllocateRecordCopy
