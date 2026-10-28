import Binary.StateRead
import NearVM.MeteredWasmCall

/-! Exact deployed prefix-length leaves764 and765. -/
namespace WNear.Binary.StateDecodePrefixLeaves
open Wasm Wasm.Near

def recordBody : Expr := [.local_get 0,.local_get 1,.store .i32 none {align:=2,offset:=4},
  .local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0}]
def recordFunction : Func := {type:=14,locals:=[],body:=recordBody,bodySize:=16}
def recordSignature : FuncType := {params:=[.num .i32,.num .i32],results:=[]}
def guard : Expr := [.local_get 1,.i32_const 4,.i32_relop .eq,.br_if 0]
def read : Expr := [.local_get 0,.load .i32 none {align:=0,offset:=0},.local_set 0,.i32_const 0,.local_set 1]
def pack : Expr := [.local_get 0,.cvt .i64_extend_i32_u,.i64_const 8,.i64_binop .shl,
  .local_get 1,.cvt .i64_extend_i32_u,.i64_binop .or]
def wordBody : Expr := [.block .empty ([.block .empty (guard++[.i32_const 1,.local_set 1,.br 1])]++read)]++pack
def wordFunction : Func := {type:=30,locals:=[],body:=wordBody,bodySize:=42}
def wordSignature : FuncType := {params:=[.num .i32,.num .i32],results:=[.num .i64]}
theorem function764 : wNearModule.funcs[716]?=some recordFunction:=by kernel_rfl
theorem function765 : wNearModule.funcs[717]?=some wordFunction:=by kernel_rfl
theorem signature764 : wNearModule.types[14]?=some recordSignature:=by kernel_rfl
theorem signature765 : wNearModule.types[30]?=some wordSignature:=by kernel_rfl

theorem activation764 (cfg : WasmConfig) (a b : UInt32) :
    activationGas cfg.regularOpCost (MeteredLogic.wasmLocals recordFunction [.i32 a,.i32 b])=9*cfg.regularOpCost:=by
  simp [activationGas,MeteredLogic.wasmLocals,recordFunction,recordBody]
theorem activation765 (cfg : WasmConfig) (a b : UInt32) :
    activationGas cfg.regularOpCost (MeteredLogic.wasmLocals wordFunction [.i32 a,.i32 b])=9*cfg.regularOpCost:=by
  simp [activationGas,MeteredLogic.wasmLocals,wordFunction,wordBody]
end WNear.Binary.StateDecodePrefixLeaves
