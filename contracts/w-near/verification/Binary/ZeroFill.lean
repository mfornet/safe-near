import Binary.Module
import NearVM.MeteredWasmCall

/-! Actual deployed f952 byte-fill loop, including paid loop backedges. -/
namespace WNear.Binary.ZeroFill
open Wasm Wasm.Near MeteredLogic

def iteration : Expr := [.local_get 3,.local_get 1,.store .i32 (some 8) {align:=0,offset:=0},
  .local_get 3,.i32_const 1,.i32_binop .add,.local_set 3,
  .local_get 2,.i32_const 4294967295,.i32_binop .add,.local_tee 2]
def loopBody : Expr := iteration++[.br_if 0]
def guarded : Expr := [.local_get 2,.i32_eqz,.br_if 0,.local_get 0,.local_set 3,.loop .empty loopBody]
def body : Expr := [.block .empty guarded,.local_get 0]
def function : Func := {type:=15,locals:=[.num .i32],body,bodySize:=44}
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[.num .i32]}
theorem module_function : wNearModule.funcs[904]? = some function := by kernel_rfl
theorem module_signature : wNearModule.types[15]? = some signature := by kernel_rfl
theorem body_eq : f952.body=body := by kernel_rfl
theorem activation (op : Nat) (ptr value len : UInt32) :
  activationGas op (wasmLocals function [.i32 ptr,.i32 value,.i32 len])=10*op := by
  simp [activationGas,wasmLocals,function,ValType.default]
end WNear.Binary.ZeroFill
