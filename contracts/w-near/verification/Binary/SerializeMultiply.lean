import Binary.Module
import NearVM.MeteredWasmCall

/-! Actual deployed compiler __multi3 leaf f954. -/
namespace WNear.Binary.SerializeMultiply
open Wasm Wasm.Near MeteredLogic

def low : Expr := [.local_get 0,.local_get 3,.i64_const 4294967295,.i64_binop .and,.local_tee 5,
  .local_get 1,.i64_const 32,.i64_binop .shr_u,.local_tee 6,.i64_binop .mul,.local_tee 7,
  .local_get 3,.i64_const 32,.i64_binop .shr_u,.local_tee 8,.local_get 1,.i64_const 4294967295,
  .i64_binop .and,.local_tee 9,.i64_binop .mul,.i64_binop .add,.local_tee 10,.i64_const 32,
  .i64_binop .shl,.local_tee 11,.local_get 5,.local_get 9,.i64_binop .mul,.i64_binop .add,
  .local_tee 5,.store .i64 none {align:=3,offset:=0}]
def high : Expr := [.local_get 0,.local_get 10,.local_get 7,.i64_relop .lt_u,.cvt .i64_extend_i32_u,
  .i64_const 32,.i64_binop .shl,.local_get 10,.i64_const 32,.i64_binop .shr_u,.i64_binop .or,
  .local_get 8,.local_get 6,.i64_binop .mul,.i64_binop .add,.local_get 5,.local_get 11,
  .i64_relop .lt_u,.cvt .i64_extend_i32_u,.i64_binop .add,.local_get 4,.local_get 1,
  .i64_binop .mul,.local_get 3,.local_get 2,.i64_binop .mul,.i64_binop .add,.i64_binop .add,
  .store .i64 none {align:=3,offset:=8}]
def body : Expr := low++high
def function : Func := {type:=8,locals:=List.replicate 7 (.num .i64),body,bodySize:=110}
def signature : FuncType := {params:=[.num .i32,.num .i64,.num .i64,.num .i64,.num .i64],results:=[]}
theorem module_function : wNearModule.funcs[906]?=some function := by kernel_rfl
theorem module_signature : wNearModule.types[8]?=some signature := by kernel_rfl
theorem low_length : low.length=31 := rfl
theorem high_length : high.length=29 := rfl
theorem body_length : body.length=60 := rfl
theorem activation (op : Nat) (out : UInt32) (aLo aHi bLo bHi : UInt64) :
    activationGas op (wasmLocals function [.i32 out,.i64 aLo,.i64 aHi,.i64 bLo,.i64 bHi])=20*op := by
  simp [activationGas,wasmLocals,function,ValType.default]
end WNear.Binary.SerializeMultiply
