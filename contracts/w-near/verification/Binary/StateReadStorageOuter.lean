import Binary.StateRead
import NearVM.MeteredWasmCall

/-! Exact deployed548 storage-read wrapper, retaining panic and missing branches. -/
namespace WNear.Binary.StateReadStorageOuter
open Wasm Wasm.Near

def reserve : Expr := [.global_get 0,.i32_const 32,.i32_binop .sub,.local_tee 3,.global_set 0]
def saveLength : Expr := [.local_get 3,.local_get 2,.store .i32 none {align:=2,offset:=12}]
def savePointer : Expr := [.local_get 3,.local_get 1,.store .i32 none {align:=2,offset:=8}]
def storageArguments : Expr := [.i32_const 1055020,.local_get 3,.i32_const 8,.i32_binop .add]
def statusGuard : Expr := [.local_tee 4,.i64_const 1,.i64_relop .gt_u,.br_if 0,.local_get 4,.cvt .i32_wrap_i64,.br_table [1,2] 1]
def panic : Expr := [.i32_const 1055964,.i32_const 40,.i32_const 1056308,.call 853,.unreachable]
def missing : Expr := [.local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0},.br 1]
def registerArguments : Expr := [.local_get 3,.i32_const 16,.i32_binop .add,.i64_const 0]
def optionArguments : Expr := [.local_get 0,.local_get 3,.i32_const 16,.i32_binop .add,.i32_const 1055256,.i32_const 68,.i32_const 1056324]
def present : Expr := registerArguments++[.call 523]++optionArguments++[.call 498]
def lookup : Expr := storageArguments++[.call 459]++statusGuard
def restore : Expr := [.local_get 3,.i32_const 32,.i32_binop .add,.global_set 0]
def body : Expr := reserve++saveLength++savePointer++[
  .block .empty ([.block .empty ([.block .empty ([.block .empty lookup]++panic)]++missing)]++present)]++restore
def function : Func := {type:=31,locals:=[.num .i32,.num .i64],body,bodySize:=163}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[]}
theorem module_function : wNearModule.funcs[500]?=some function := by kernel_rfl
theorem module_type : wNearModule.types[31]?=some signature := by kernel_rfl
theorem activation (op : Nat) (out key len : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 key,.i32 len])=11*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.StateReadStorageOuter
