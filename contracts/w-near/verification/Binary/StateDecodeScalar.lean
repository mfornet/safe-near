import Binary.StateDecodeWords
import Binary.StateDecodeSlices

/-! Exact deployed Borsh scalar wrappers f372 (U128) and f371 (U64). -/
namespace WNear.Binary.StateDecodeScalar
open Wasm Wasm.Near

def width (wide : Bool) : UInt32 := if wide then 16 else 8
def location (wide : Bool) : UInt32 := if wide then 1052272 else 1052256
def takeOffset (wide : Bool) : UInt32 := if wide then 8 else 16
def wordOffset (wide : Bool) : UInt32 := if wide then 16 else 24
def setup : Expr := [.global_get 0,.i32_const 48,.i32_binop .sub,.local_tee 2,.global_set 0]
def lengthGuard (wide : Bool) : Expr := [.local_get 1,.load .i32 none {align:=2,offset:=4},.local_tee 3,
  .i32_const (width wide-1),.i32_relop .gt_u,.br_if 0]
def tooShort : Expr := [.local_get 0,.i32_const 11,.i32_const 1052128,.i32_const 26,.call 736,
  .store .i64 none {align:=2,offset:=4},.i32_const 1,.local_set 1,.br 1]
def takeArguments (wide : Bool) : Expr := [.local_get 2,.i32_const (takeOffset wide),.i32_binop .add,
  .local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 3,.i32_const (width wide),.i32_const (location wide),.call 362]
def wordArguments (wide : Bool) : Expr := [.local_get 2,.i32_const (wordOffset wide),.i32_binop .add,
  .local_get 2,.load .i32 none {align:=2,offset:=(takeOffset wide).toNat},
  .local_get 2,.load .i32 none {align:=2,offset:=(takeOffset wide).toNat+4},.call (if wide then 694 else 710)]
def statusGuard (wide : Bool) : Expr := [.local_get 2,.load .i32 (some {bits:=8,signed:=false}) {align:=0,offset:=(wordOffset wide).toNat},
  .i32_const 1,.i32_relop .eq,.br_if 1]
def cache (wide : Bool) : Expr := if wide then
  [.local_get 2,.i32_const 25,.i32_binop .add,.load .i64 none {align:=0,offset:=0},.local_set 4,
   .local_get 2,.load .i64 none {align:=0,offset:=17},.local_set 5]
  else [.local_get 2,.load .i64 none {align:=0,offset:=25},.local_set 4]
def dropArguments (wide : Bool) : Expr := [.local_get 2]++(if wide then [] else [.i32_const 8,.i32_binop .add])++
  [.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 1,.load .i32 none {align:=2,offset:=4},
   .i32_const (width wide),.i32_const (location wide),.call 361]
def dropCache (wide : Bool) : Expr := [.local_get 2,.load .i64 none {align:=3,offset:=if wide then 0 else 8},
  .local_set (if wide then 6 else 5)]
def outputValues (wide : Bool) : Expr := if wide then
  [.local_get 0,.i32_const 16,.i32_binop .add,.local_get 4,.store .i64 none {align:=3,offset:=0},
   .local_get 0,.i32_const 8,.i32_binop .add,.local_get 5,.store .i64 none {align:=3,offset:=0}]
  else [.local_get 0,.i32_const 8,.i32_binop .add,.local_get 4,.store .i64 none {align:=3,offset:=0}]
def updateSlice (wide : Bool) : Expr := [.local_get 1,.local_get (if wide then 6 else 5),
  .store .i64 none {align:=2,offset:=0},.i32_const 0,.local_set 1]
def accepted (wide : Bool) : Expr := takeArguments wide++wordArguments wide++statusGuard wide++cache wide++
  dropArguments wide++dropCache wide++outputValues wide++updateSlice wide
def finish : Expr := [.local_get 0,.local_get 1,.store .i32 none {align:=2,offset:=0},
  .local_get 2,.i32_const 48,.i32_binop .add,.global_set 0,.return]
def invalid (wide : Bool) : Expr := [.i32_const 1052068,.i32_const 43,.local_get 2,.i32_const 40,.i32_binop .add,
  .i32_const 1052112,.i32_const (location wide),.call 881,.unreachable]
def body (wide : Bool) : Expr := setup++[.block .empty
  ([.block .empty ([.block .empty (lengthGuard wide++tooShort)]++accepted wide)]++finish)]++invalid wide
def function (wide : Bool) : Func :=
  {type:=14, locals:=[.num .i32,.num .i32,.num .i64,.num .i64]++(if wide then [.num .i64] else []),
   body:=body wide, bodySize:=if wide then 260 else 243}
def signature : FuncType := {params:=[.num .i32,.num .i32],results:=[]}
theorem function372 : wNearModule.funcs[324]?=some (function true) := by kernel_rfl
theorem function371 : wNearModule.funcs[323]?=some (function false) := by kernel_rfl
theorem module_type : wNearModule.types[14]?=some signature := by kernel_rfl
end WNear.Binary.StateDecodeScalar
