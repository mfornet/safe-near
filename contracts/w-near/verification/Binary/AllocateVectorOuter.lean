import Binary.Module
import NearVM.MeteredWasmCall

/-! Actual f687 byte-flag dispatch and cached vector record copy. -/
namespace WNear.Binary.AllocateVectorOuter
open Wasm Wasm.Near

def reserve : Expr := [.global_get 0,.i32_const 32,.i32_binop .sub,.local_tee 3,.global_set 0]
def arguments : Expr := [.local_get 3,.i32_const 8,.i32_binop .add,.local_get 2,.i32_const 1]
def cache : Expr := [.local_get 3,.load .i64 none {align:=3,offset:=8},.local_set 4]
def output : Expr := [.local_get 0,.local_get 2,.store .i32 none {align:=2,offset:=8},
  .local_get 0,.local_get 4,.store .i64 none {align:=2,offset:=0}]
def restore : Expr := [.local_get 3,.i32_const 32,.i32_binop .add,.global_set 0]
def accepted : Expr := [.local_get 1,.i32_const 255,.i32_binop .and,.br_if 0] ++
  arguments ++ [.call 686] ++ cache ++ output ++ [.br 1]
def alternative : Expr := [.local_get 3,.i32_const 16,.i32_binop .add,.local_get 2,.call 681,
  .local_get 3,.load .i32 none {align:=2,offset:=16},.local_get 1,.local_get 2,.call 952,.drop,
  .local_get 0,.i32_const 8,.i32_binop .add,.local_get 2,.store .i32 none {align:=2,offset:=0},
  .local_get 0,.local_get 3,.load .i64 none {align:=3,offset:=16},.store .i64 none {align:=2,offset:=0}]
def body : Expr := reserve ++ [.block .empty ([.block .empty accepted]++alternative)] ++ restore
def function : Func := {type:=31,locals:=[.num .i32,.num .i64],body,bodySize:=135}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[]}
set_option maxRecDepth 20000

theorem module_function : wNearModule.funcs[639]?=some function := by kernel_rfl
theorem module_type : wNearModule.types[31]?=some signature := by kernel_rfl
theorem activation (op : Nat) (out flag count : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 flag,.i32 count])=11*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.AllocateVectorOuter
