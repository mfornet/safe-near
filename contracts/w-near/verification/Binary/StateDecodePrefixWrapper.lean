import Binary.StateDecodePrefix

/-! Exact315 result wrapper. The accepted tag path bypasses the real760
error conversion, after caching its packed result before output writes. -/
namespace WNear.Binary.StateDecodePrefixWrapper
open Wasm Wasm.Near

def setup : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 2,.global_set 0]
def arguments : Expr := [.local_get 2,.local_get 1]
def cache : Expr := [.i32_const 1,.local_set 1,.local_get 2,.load .i64 none {align:=2,offset:=4},.local_set 3]
def guard : Expr := [.local_get 2,.load .i32 none {align:=2,offset:=0},.i32_const 1,.i32_relop .eq,.br_if 0]
def copy : Expr := [.local_get 2,.i32_const 12,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.local_set 1,
  .local_get 0,.local_get 3,.store .i64 none {align:=2,offset:=4},
  .local_get 0,.i32_const 12,.i32_binop .add,.local_get 1,.store .i32 none {align:=2,offset:=0},
  .i32_const 0,.local_set 1,.br 1]
def rejected : Expr := [.local_get 0,.local_get 3,.call 760,.store .i64 none {align:=2,offset:=4}]
def finish : Expr := [.local_get 0,.local_get 1,.store .i32 none {align:=2,offset:=0},.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]
def body : Expr := setup++arguments++[.call 316]++cache++[.block .empty ([.block .empty (guard++copy)]++rejected)]++finish
def signature : FuncType := {params:=[.num .i32,.num .i32],results:=[]}
def function : Func := {type:=14,locals:=[.num .i32,.num .i64],body,bodySize:=124}

theorem exact_function : WNear.Binary.f315=function:=by kernel_rfl
theorem module_function : wNearModule.funcs[267]?=some function:=by kernel_rfl
theorem module_signature : wNearModule.types[14]?=some signature:=by kernel_rfl
theorem activation_cost (op : Nat) (out slice : UInt32) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 slice])=11*op:=by
  simp[activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.StateDecodePrefixWrapper
