import Binary.StateRead
import NearVM.MeteredWasmCall

/-! The deployed523 Option<Vec<u8>> register reader, retaining both branches. -/
namespace WNear.Binary.StateReadRegisterOuter
open Wasm Wasm.Near

def reserve : Expr := [.global_get 0,.i32_const 48,.i32_binop .sub,.local_tee 2,.global_set 0]
def saveRegister : Expr := [.local_get 2,.local_get 1,.store .i64 none {align:=3,offset:=24}]
def lengthArguments : Expr := [.local_get 2,.i32_const 8,.i32_binop .add,.local_get 1]
def presentGuard : Expr := [.local_get 2,.load .i64 none {align:=3,offset:=8},.cvt .i32_wrap_i64,.i32_eqz,.br_if 0]
def vectorArguments : Expr := [.local_get 2,.i32_const 32,.i32_binop .add,.i32_const 0,
  .local_get 2,.load .i64 none {align:=3,offset:=16},.cvt .i32_wrap_i64]
def readArguments : Expr := [.i32_const 1055020,.local_get 2,.i32_const 24,.i32_binop .add,
  .local_get 2,.i32_const 32,.i32_binop .add]
def copyHigh : Expr := [.local_get 0,.i32_const 8,.i32_binop .add,.local_get 2,.i32_const 32,
  .i32_binop .add,.i32_const 8,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0}]
def copyLow : Expr := [.local_get 0,.local_get 2,.load .i64 none {align:=3,offset:=32},.store .i64 none {align:=2,offset:=0}]
def restore : Expr := [.local_get 2,.i32_const 48,.i32_binop .add,.global_set 0]
def present : Expr := presentGuard++vectorArguments++[.call 687]++readArguments++[.call 435]++copyHigh++copyLow++[.br 1]
def absent : Expr := [.call 761,.local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0}]
def body : Expr := reserve++saveRegister++lengthArguments++[.call 524,.block .empty ([.block .empty present]++absent)]++restore
def function : Func := {type:=5,locals:=[.num .i32],body,bodySize:=152}
def signature : FuncType := {params:=[.num .i32,.num .i64],results:=[]}
theorem module_function : wNearModule.funcs[475]?=some function := by kernel_rfl
theorem module_type : wNearModule.types[5]?=some signature := by kernel_rfl
theorem activation (op : Nat) (out : UInt32) (register : UInt64) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i64 register])=10*op := by
  simp [activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.StateReadRegisterOuter
