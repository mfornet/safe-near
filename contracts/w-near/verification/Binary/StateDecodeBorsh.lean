import Binary.StateDecodePrefixWrapper
import Binary.StateDecodeScalar

/-! Exact deployed425 Borsh state decoder. The accepted route calls315,372,
and371; rejected routes retain their actual760 conversions and321 cleanup. -/
namespace WNear.Binary.StateDecodeBorsh
open Wasm Wasm.Near

def body : Expr := [.global_get 0,
  .i32_const 96,
  .i32_binop .sub,
  .local_tee 2,
  .global_set 0,
  .local_get 2,
  .i32_const 56,
  .i32_binop .add,
  .local_get 1,
  .call 315,
  .local_get 2,
  .load .i64 none { align := 2, offset := 60 },
  .local_set 3,
  .block
  .empty
  [.block
  .empty
  [.block
  .empty
  [.local_get 2,
  .load .i32 none { align := 2, offset := 56 },
  .i32_const 1,
  .i32_relop .eq,
  .br_if 0,
  .local_get 2,
  .local_get 2,
  .i32_const 68,
  .i32_binop .add,
  .local_tee 4,
  .load .i32 none { align := 2, offset := 0 },
  .store .i32 none { align := 2, offset := 24 },
  .local_get 2,
  .local_get 3,
  .store .i64 none { align := 3, offset := 16 },
  .local_get 2,
  .i32_const 56,
  .i32_binop .add,
  .local_get 1,
  .call 372,
  .local_get 2,
  .i32_const 32,
  .i32_binop .add,
  .i32_const 8,
  .i32_binop .add,
  .local_get 4,
  .load .i64 none { align := 2, offset := 0 },
  .store .i64 none { align := 3, offset := 0 },
  .local_get 2,
  .i32_const 48,
  .i32_binop .add,
  .local_get 2,
  .i32_const 76,
  .i32_binop .add,
  .load .i32 none { align := 2, offset := 0 },
  .store .i32 none { align := 2, offset := 0 },
  .local_get 2,
  .local_get 2,
  .load .i64 none { align := 2, offset := 60 },
  .store .i64 none { align := 3, offset := 32 },
  .local_get 2,
  .load .i32 none { align := 2, offset := 56 },
  .i32_const 1,
  .i32_relop .eq,
  .br_if 1,
  .local_get 2,
  .i32_const 32,
  .i32_binop .add,
  .i32_const 12,
  .i32_binop .add,
  .load .i64 none { align := 2, offset := 0 },
  .local_set 3,
  .local_get 2,
  .load .i64 none { align := 2, offset := 36 },
  .local_set 5,
  .local_get 2,
  .i32_const 56,
  .i32_binop .add,
  .local_get 1,
  .call 371,
  .local_get 2,
  .i32_const 80,
  .i32_binop .add,
  .i32_const 8,
  .i32_binop .add,
  .local_get 2,
  .i32_const 56,
  .i32_binop .add,
  .i32_const 12,
  .i32_binop .add,
  .load .i32 none { align := 2, offset := 0 },
  .store .i32 none { align := 2, offset := 0 },
  .local_get 2,
  .local_get 2,
  .load .i64 none { align := 2, offset := 60 },
  .store .i64 none { align := 3, offset := 80 },
  .block
  .empty
  [.local_get 2,
  .load .i32 none { align := 2, offset := 56 },
  .i32_const 1,
  .i32_relop .eq,
  .br_if 0,
  .local_get 2,
  .i32_const 8,
  .i32_binop .add,
  .local_get 2,
  .i32_const 16,
  .i32_binop .add,
  .i32_const 8,
  .i32_binop .add,
  .load .i32 none { align := 2, offset := 0 },
  .local_tee 1,
  .store .i32 none { align := 2, offset := 0 },
  .local_get 2,
  .local_get 2,
  .load .i64 none { align := 3, offset := 16 },
  .local_tee 6,
  .store .i64 none { align := 3, offset := 0 },
  .local_get 2,
  .load .i64 none { align := 2, offset := 84 },
  .local_set 7,
  .local_get 0,
  .i32_const 16,
  .i32_binop .add,
  .local_get 3,
  .store .i64 none { align := 3, offset := 0 },
  .local_get 0,
  .i32_const 8,
  .i32_binop .add,
  .local_get 5,
  .store .i64 none { align := 3, offset := 0 },
  .local_get 0,
  .i32_const 24,
  .i32_binop .add,
  .local_get 7,
  .store .i64 none { align := 3, offset := 0 },
  .local_get 0,
  .i32_const 32,
  .i32_binop .add,
  .local_get 6,
  .store .i64 none { align := 3, offset := 0 },
  .local_get 0,
  .i32_const 40,
  .i32_binop .add,
  .local_get 1,
  .store .i32 none { align := 2, offset := 0 },
  .local_get 0,
  .i32_const 0,
  .store .i32 none { align := 2, offset := 0 },
  .br 3],
  .local_get 2,
  .load .i64 none { align := 3, offset := 80 },
  .call 760,
  .local_set 3,
  .local_get 0,
  .i32_const 1,
  .store .i32 none { align := 2, offset := 0 },
  .local_get 0,
  .local_get 3,
  .store .i64 none { align := 2, offset := 4 },
  .local_get 2,
  .i32_const 16,
  .i32_binop .add,
  .call 321,
  .br 2],
  .local_get 3,
  .call 760,
  .local_set 3,
  .local_get 0,
  .i32_const 1,
  .store .i32 none { align := 2, offset := 0 },
  .local_get 0,
  .local_get 3,
  .store .i64 none { align := 2, offset := 4 },
  .br 1],
  .local_get 2,
  .load .i64 none { align := 3, offset := 32 },
  .call 760,
  .local_set 3,
  .local_get 0,
  .i32_const 1,
  .store .i32 none { align := 2, offset := 0 },
  .local_get 0,
  .local_get 3,
  .store .i64 none { align := 2, offset := 4 },
  .local_get 2,
  .i32_const 16,
  .i32_binop .add,
  .call 321],
  .local_get 2,
  .i32_const 96,
  .i32_binop .add,
  .global_set 0]
def setup : Expr := [.global_get 0,.i32_const 96,.i32_binop .sub,.local_tee 2,.global_set 0]
def prefixArguments : Expr := [.local_get 2,.i32_const 56,.i32_binop .add,.local_get 1]
def cachePrefix : Expr := [.local_get 2,.load .i64 none {align:=2,offset:=60},.local_set 3]
def prefixGuard : Expr := [.local_get 2,.load .i32 none {align:=2,offset:=56},.i32_const 1,.i32_relop .eq,.br_if 0]
def savePrefix : Expr := [.local_get 2,.local_get 2,.i32_const 68,.i32_binop .add,.local_tee 4,
  .load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=24},
  .local_get 2,.local_get 3,.store .i64 none {align:=3,offset:=16}]
def scalarArguments : Expr := [.local_get 2,.i32_const 56,.i32_binop .add,.local_get 1]
def saveWide : Expr := [.local_get 2,.i32_const 32,.i32_binop .add,.i32_const 8,.i32_binop .add,
  .local_get 4,.load .i64 none {align:=2,offset:=0},.store .i64 none {align:=3,offset:=0},
  .local_get 2,.i32_const 48,.i32_binop .add,.local_get 2,.i32_const 76,.i32_binop .add,
  .load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0},
  .local_get 2,.local_get 2,.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=32}]
def wideGuard : Expr := [.local_get 2,.load .i32 none {align:=2,offset:=56},.i32_const 1,.i32_relop .eq,.br_if 1]
def cacheWide : Expr := [.local_get 2,.i32_const 32,.i32_binop .add,.i32_const 12,.i32_binop .add,
  .load .i64 none {align:=2,offset:=0},.local_set 3,.local_get 2,.load .i64 none {align:=2,offset:=36},.local_set 5]
def saveNarrow : Expr := [.local_get 2,.i32_const 80,.i32_binop .add,.i32_const 8,.i32_binop .add,
  .local_get 2,.i32_const 56,.i32_binop .add,.i32_const 12,.i32_binop .add,
  .load .i32 none {align:=2,offset:=0},.store .i32 none {align:=2,offset:=0},
  .local_get 2,.local_get 2,.load .i64 none {align:=2,offset:=60},.store .i64 none {align:=3,offset:=80}]
def narrowGuard : Expr := [.local_get 2,.load .i32 none {align:=2,offset:=56},.i32_const 1,.i32_relop .eq,.br_if 0]
def cacheVector : Expr := [.local_get 2,.i32_const 8,.i32_binop .add,.local_get 2,.i32_const 16,.i32_binop .add,
  .i32_const 8,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.local_tee 1,.store .i32 none {align:=2,offset:=0},
  .local_get 2,.local_get 2,.load .i64 none {align:=3,offset:=16},.local_tee 6,.store .i64 none {align:=3,offset:=0}]
def cacheNarrow : Expr := [.local_get 2,.load .i64 none {align:=2,offset:=84},.local_set 7]
def output : Expr := [.local_get 0,.i32_const 16,.i32_binop .add,.local_get 3,.store .i64 none {align:=3,offset:=0},
  .local_get 0,.i32_const 8,.i32_binop .add,.local_get 5,.store .i64 none {align:=3,offset:=0},
  .local_get 0,.i32_const 24,.i32_binop .add,.local_get 7,.store .i64 none {align:=3,offset:=0},
  .local_get 0,.i32_const 32,.i32_binop .add,.local_get 6,.store .i64 none {align:=3,offset:=0},
  .local_get 0,.i32_const 40,.i32_binop .add,.local_get 1,.store .i32 none {align:=2,offset:=0},
  .local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0}]
def prefixRejected : Expr := [.local_get 3,.call 760,.local_set 3,.local_get 0,.i32_const 1,.store .i32 none {align:=2,offset:=0},
  .local_get 0,.local_get 3,.store .i64 none {align:=2,offset:=4},.br 1]
def narrowRejected : Expr := [.local_get 2,.load .i64 none {align:=3,offset:=80},.call 760,.local_set 3,
  .local_get 0,.i32_const 1,.store .i32 none {align:=2,offset:=0},.local_get 0,.local_get 3,.store .i64 none {align:=2,offset:=4},
  .local_get 2,.i32_const 16,.i32_binop .add,.call 321,.br 2]
def wideRejected : Expr := [.local_get 2,.load .i64 none {align:=3,offset:=32},.call 760,.local_set 3,
  .local_get 0,.i32_const 1,.store .i32 none {align:=2,offset:=0},.local_get 0,.local_get 3,.store .i64 none {align:=2,offset:=4},
  .local_get 2,.i32_const 16,.i32_binop .add,.call 321]
def restore : Expr := [.local_get 2,.i32_const 96,.i32_binop .add,.global_set 0]
def acceptedNarrow : Expr := narrowGuard++cacheVector++cacheNarrow++output++[.br 3]
def accepted : Expr := prefixGuard++savePrefix++scalarArguments++[.call 372]++saveWide++wideGuard++cacheWide++
  scalarArguments++[.call 371]++saveNarrow++[.block .empty acceptedNarrow]++narrowRejected
def structuredBody : Expr := setup++prefixArguments++[.call 315]++cachePrefix++
  [.block .empty ([.block .empty ([.block .empty accepted]++prefixRejected)]++wideRejected)]++restore

theorem body_segments : body=structuredBody:=by kernel_rfl

/-- Static accepted-path recipe. This is a segmentation/counting aid, not an
execution theorem; the four actual block entries are retained in structuredBody. -/
def acceptedRecipe : Expr := setup++prefixArguments++[.call 315]++cachePrefix++prefixGuard++savePrefix++
  scalarArguments++[.call 372]++saveWide++wideGuard++cacheWide++scalarArguments++[.call 371]++
  saveNarrow++narrowGuard++cacheVector++cacheNarrow++output++[.br 3]++restore

theorem accepted_calls : acceptedRecipe.filterMap (fun i=>match i with|.call n=>some n|_=>none)=[315,372,371]:=by kernel_rfl
theorem accepted_scalar_count : acceptedRecipe.length-3=143:=by kernel_rfl
theorem output_length : output.length=28:=by kernel_rfl
theorem cacheVector_length : cacheVector.length=16:=by kernel_rfl
theorem saveWide_length : saveWide.length=20:=by kernel_rfl
theorem saveNarrow_length : saveNarrow.length=16:=by kernel_rfl

def function : Func := {type:=14,locals:=[.num .i32,.num .i64,.num .i32,.num .i64,.num .i64,.num .i64],body,bodySize:=450}
def signature : FuncType := {params:=[.num .i32,.num .i32],results:=[]}

theorem exact_function : WNear.Binary.f425=function:=by kernel_rfl
theorem module_function : wNearModule.funcs[377]?=some function:=by kernel_rfl
theorem module_signature : wNearModule.types[14]?=some signature:=by kernel_rfl
theorem body_length : body.length=18:=by kernel_rfl

theorem activation_cost(op:Nat)(out slice:UInt32):
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 slice])=14*op:=by
  simp[activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.StateDecodeBorsh
