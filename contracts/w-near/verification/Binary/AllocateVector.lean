import Binary.AllocateRecordCopy

/-! The actual686 vector allocation path, including both deployed failure tails. -/
namespace WNear.Binary.AllocateVector
open Wasm Wasm.Near

def reserve : Expr := [.global_get 0,.i32_const 32,.i32_binop .sub,.local_tee 3,.global_set 0]
def layoutArguments : Expr := [.local_get 3,.i32_const 24,.i32_binop .add,.local_get 1]
def guard : Expr := [.local_get 3,.load .i32 none {align:=2,offset:=28},.local_tee 1,
  .i32_eqz,.br_if 0,.local_get 3,.load .i32 none {align:=2,offset:=24},
  .local_tee 4,.i32_const 4294967295,.i32_relop .le_s,.br_if 0]
def allocateArguments : Expr := [.local_get 3,.i32_const 8,.i32_binop .add,.local_get 4,.local_get 1]
def cache : Expr := [.local_get 3,.load .i32 none {align:=2,offset:=12},.local_set 5,
  .local_get 3,.load .i32 none {align:=2,offset:=8},.local_set 2]
def alternateArguments : Expr := [.local_get 3,.i32_const 16,.i32_binop .add,.local_get 4,.local_get 1]
def alternateCache : Expr := [.local_get 3,.load .i32 none {align:=2,offset:=20},.local_set 5,
  .local_get 3,.load .i32 none {align:=2,offset:=16},.local_set 2]
def select : Expr := [.local_get 2,.i32_eqz,.br_if 0]
def nonzero : Expr := [.local_get 2,.i32_eqz,.br_if 1]
def record : Expr := [.local_get 0,.local_get 2,.store .i32 none {align:=2,offset:=0},
  .local_get 0,.local_get 5,.store .i32 none {align:=2,offset:=4}]
def restore : Expr := [.local_get 3,.i32_const 32,.i32_binop .add,.global_set 0]
def allocation : Expr := [.block .empty (select ++ allocateArguments ++ [.call 690] ++ cache ++ [.br 1])] ++
  alternateArguments ++ [.call 688] ++ alternateCache

def accepted : Expr := [.block .empty allocation] ++ nonzero ++ record ++ restore ++ [.return]
def checked : Expr := guard ++ accepted
def body : Expr := reserve ++ layoutArguments ++ [.call 685,
  .block .empty ([.block .empty checked,.call 844,.unreachable]),
  .local_get 4,.local_get 1,.call 842,.unreachable]
def function : Func := {type:=31,locals:=[.num .i32,.num .i32,.num .i32],body,bodySize:=182}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[]}
theorem module_function : wNearModule.funcs[638]?=some function := by kernel_rfl
theorem module_type : wNearModule.types[31]?=some signature := by kernel_rfl
theorem activation (op : Nat) (out size flag : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 size,.i32 flag])=11*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.AllocateVector
