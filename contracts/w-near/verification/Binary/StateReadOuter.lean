import Binary.StateRead
import NearVM.MeteredWasmCall

/-! Literal deployed219 state-read wrapper and its successful storage/decode
segments. This metadata does not assume or prove whole219 execution. -/
namespace WNear.Binary.StateReadOuter
open Wasm Wasm.Near

def function : Func :=
{ type := 0,
  locals := [Wasm.ValType.num (Wasm.NumType.i32)],
  body := [Wasm.Instr.global_get 0,
           Wasm.Instr.i32_const 96,
           Wasm.Instr.i32_binop (Wasm.IBinOp.sub),
           Wasm.Instr.local_tee 1,
           Wasm.Instr.global_set 0,
           Wasm.Instr.local_get 1,
           Wasm.Instr.i32_const 8,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.i32_const 1049788,
           Wasm.Instr.i32_const 5,
           Wasm.Instr.call 548,
           Wasm.Instr.block
             (Wasm.BlockType.empty)
             [Wasm.Instr.block
                (Wasm.BlockType.empty)
                [Wasm.Instr.block
                   (Wasm.BlockType.empty)
                   [Wasm.Instr.local_get 1,
                    Wasm.Instr.load (Wasm.NumType.i32) none { align := 2, offset := 8 },
                    Wasm.Instr.br_if 0,
                    Wasm.Instr.local_get 0,
                    Wasm.Instr.i32_const 0,
                    Wasm.Instr.store (Wasm.NumType.i32) none { align := 2, offset := 24 },
                    Wasm.Instr.br 1],
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.i32_const 24,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.i32_const 8,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.i32_const 8,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.i32_const 8,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.load (Wasm.NumType.i32) none { align := 2, offset := 0 },
                 Wasm.Instr.store (Wasm.NumType.i32) none { align := 2, offset := 0 },
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.load (Wasm.NumType.i64) none { align := 3, offset := 8 },
                 Wasm.Instr.store (Wasm.NumType.i64) none { align := 3, offset := 24 },
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.i32_const 24,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.call 779,
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.i32_const 40,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.load (Wasm.NumType.i32) none { align := 2, offset := 0 },
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.load (Wasm.NumType.i32) none { align := 2, offset := 4 },
                 Wasm.Instr.call 161,
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.load (Wasm.NumType.i32) none { align := 2, offset := 40 },
                 Wasm.Instr.i32_const 1,
                 Wasm.Instr.i32_relop (Wasm.IRelOp.eq),
                 Wasm.Instr.br_if 1,
                 Wasm.Instr.local_get 0,
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.i32_const 40,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.i32_const 8,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.i32_const 40,
                 Wasm.Instr.call 951,
                 Wasm.Instr.drop,
                 Wasm.Instr.local_get 1,
                 Wasm.Instr.i32_const 24,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.call 68],
              Wasm.Instr.local_get 1,
              Wasm.Instr.i32_const 96,
              Wasm.Instr.i32_binop (Wasm.IBinOp.add),
              Wasm.Instr.global_set 0,
              Wasm.Instr.return],
           Wasm.Instr.local_get 1,
           Wasm.Instr.local_get 1,
           Wasm.Instr.load (Wasm.NumType.i64) none { align := 2, offset := 44 },
           Wasm.Instr.store (Wasm.NumType.i64) none { align := 3, offset := 88 },
           Wasm.Instr.i32_const 1049793,
           Wasm.Instr.i32_const 38,
           Wasm.Instr.local_get 1,
           Wasm.Instr.i32_const 88,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.i32_const 1049052,
           Wasm.Instr.i32_const 1049928,
           Wasm.Instr.call 881,
           Wasm.Instr.unreachable],
  bodySize := 228 }
def body : Expr := function.body
def signature : FuncType := {params:=[.num .i32],results:=[]}
private def blockBody (i:Instr):Expr:=match i with |.block _ code=>code|_=>[]
def setup : Expr := body.take 5
def storageArguments : Expr := (body.drop 5).take 5
def outerBody : Expr := blockBody body[11]!
def presentBody : Expr := blockBody outerBody[0]!
def presenceBody : Expr := blockBody presentBody[0]!
def presenceGuard : Expr := presenceBody.take 3
def copyStorage : Expr := (presentBody.drop 1).take 16
def packSlice : Expr := (presentBody.drop 17).take 5
def decode : Expr := (presentBody.drop 22).take 8
def tagGuard : Expr := (presentBody.drop 30).take 5
def copyResult : Expr := (presentBody.drop 35).take 9
def release : Expr := presentBody.drop 44
def restoreReturn : Expr := outerBody.drop 1
def rejected : Expr := body.drop 12

theorem exact_function : WNear.Binary.f219=function:=by kernel_rfl
theorem module_function : wNearModule.funcs[171]?=some function:=by kernel_rfl
theorem module_signature : wNearModule.types[0]?=some signature:=by kernel_rfl
theorem body_segments : body=setup++storageArguments++[.call 548]++[.block .empty outerBody]++rejected:=by kernel_rfl
theorem outer_segments : outerBody=[.block .empty presentBody]++restoreReturn:=by kernel_rfl
theorem present_segments : presentBody=[.block .empty presenceBody]++copyStorage++packSlice++decode++tagGuard++copyResult++release:=by kernel_rfl
theorem presence_guard : presenceGuard=[.local_get 1,.load .i32 none {align:=2,offset:=8},.br_if 0]:=by kernel_rfl
theorem restore_return : restoreReturn=[.local_get 1,.i32_const 96,.i32_binop .add,.global_set 0,.return]:=by kernel_rfl
def acceptedRecipe : Expr := setup++storageArguments++[.call 548]++presenceGuard++copyStorage++packSlice++decode++tagGuard++copyResult++release++restoreReturn
theorem accepted_calls : acceptedRecipe.filterMap (fun i=>match i with |.call n=>some n|_=>none)=[548,779,161,951,68]:=by kernel_rfl
theorem accepted_recipe_length : acceptedRecipe.length=66:=by kernel_rfl
theorem activation_cost(op:Nat)(out:UInt32): activationGas op (MeteredLogic.wasmLocals function [.i32 out])=9*op:=by
  simp[activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.StateReadOuter
