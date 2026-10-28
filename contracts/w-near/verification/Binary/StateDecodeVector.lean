import Binary.StateDecodePrefix

/-! Exact deployed byte-vector construction wrappers373 and374. -/
namespace WNear.Binary.StateDecodeVector
open Wasm Wasm.Near

def setup : Expr := [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee 2,.global_set 0]
def arguments : Expr := [.local_get 2,.i32_const 8,.i32_binop .add,.local_get 1,.i32_const 0]
def cache : Expr := [.local_get 2,.load .i64 none {align:=3,offset:=8},.local_set 3]
def output : Expr := [.local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=8},
  .local_get 0,.local_get 3,.store .i64 none {align:=2,offset:=0}]
def restore : Expr := [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]
def body : Expr := setup++arguments++[.call 767]++cache++output++restore
def function : Func := {type:=14,locals:=[.num .i32,.num .i64],body,bodySize:=70}
def signature : FuncType := {params:=[.num .i32,.num .i32],results:=[]}

def copyBody : Expr := [.local_get 0,.local_get 2,.call 373,.local_get 0,.load .i32 none {align:=2,offset:=0},
  .local_get 1,.local_get 2,.call 951,.drop,.local_get 0,.local_get 2,.store .i32 none {align:=2,offset:=8}]
def copyFunction : Func := {type:=31,locals:=[],body:=copyBody,bodySize:=35}
def copySignature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[]}

theorem function373 : wNearModule.funcs[325]?=some function:=by kernel_rfl
theorem function374 : wNearModule.funcs[326]?=some copyFunction:=by kernel_rfl
theorem module_signature373 : wNearModule.types[14]?=some signature:=by kernel_rfl
theorem module_signature374 : wNearModule.types[31]?=some copySignature:=by kernel_rfl

theorem activation373 (op:Nat) (out size:UInt32) :
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 size])=11*op:=by
  simp[activationGas,MeteredLogic.wasmLocals,function,ValType.default]
theorem activation374 (op:Nat) (out source size:UInt32) :
    activationGas op (MeteredLogic.wasmLocals copyFunction [.i32 out,.i32 source,.i32 size])=10*op:=by
  simp[activationGas,MeteredLogic.wasmLocals,copyFunction]
end WNear.Binary.StateDecodeVector
