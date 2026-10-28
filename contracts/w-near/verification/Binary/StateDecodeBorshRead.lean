import Binary.StateDecodeBorshWrapper

/-! Exact deployed161 Borsh byte-slice entry. Metadata and segmentation only;
accepted nested calls and their exhausted-input guard remain execution work. -/
namespace WNear.Binary.StateDecodeBorshRead
open Wasm Wasm.Near

def function : Func := {
  type := 31,
  locals := [Wasm.ValType.num (Wasm.NumType.i32), Wasm.ValType.num (Wasm.NumType.i64)],
  body := [Wasm.Instr.global_get 0,
           Wasm.Instr.i32_const 144,
           Wasm.Instr.i32_binop (Wasm.IBinOp.sub),
           Wasm.Instr.local_tee 3,
           Wasm.Instr.global_set 0,
           Wasm.Instr.local_get 3,
           Wasm.Instr.local_get 2,
           Wasm.Instr.store (Wasm.NumType.i32) none { align := 2, offset := 12 },
           Wasm.Instr.local_get 3,
           Wasm.Instr.local_get 1,
           Wasm.Instr.store (Wasm.NumType.i32) none { align := 2, offset := 8 },
           Wasm.Instr.local_get 3,
           Wasm.Instr.i32_const 96,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.local_get 3,
           Wasm.Instr.i32_const 8,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.call 162,
           Wasm.Instr.local_get 3,
           Wasm.Instr.load (Wasm.NumType.i64) none { align := 2, offset := 100 },
           Wasm.Instr.local_set 4,
           Wasm.Instr.local_get 3,
           Wasm.Instr.load (Wasm.NumType.i32) none { align := 2, offset := 96 },
           Wasm.Instr.local_set 1,
           Wasm.Instr.local_get 3,
           Wasm.Instr.i32_const 60,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.local_get 3,
           Wasm.Instr.i32_const 108,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.i32_const 36,
           Wasm.Instr.call 951,
           Wasm.Instr.drop,
           Wasm.Instr.block
             (Wasm.BlockType.empty)
             [Wasm.Instr.block
                (Wasm.BlockType.empty)
                [Wasm.Instr.local_get 1,
                 Wasm.Instr.i32_const 1,
                 Wasm.Instr.i32_relop (Wasm.IRelOp.eq),
                 Wasm.Instr.br_if 0,
                 Wasm.Instr.local_get 3,
                 Wasm.Instr.local_get 4,
                 Wasm.Instr.i64_const 32,
                 Wasm.Instr.i64_binop (Wasm.IBinOp.shr_u),
                 Wasm.Instr.store (Wasm.NumType.i64) (some 32) { align := 2, offset := 16 },
                 Wasm.Instr.local_get 3,
                 Wasm.Instr.i32_const 16,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.i32_const 4,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.or),
                 Wasm.Instr.local_get 3,
                 Wasm.Instr.i32_const 60,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.i32_const 36,
                 Wasm.Instr.call 951,
                 Wasm.Instr.drop,
                 Wasm.Instr.block
                   (Wasm.BlockType.empty)
                   [Wasm.Instr.local_get 3,
                    Wasm.Instr.load (Wasm.NumType.i32) none { align := 2, offset := 12 },
                    Wasm.Instr.i32_eqz,
                    Wasm.Instr.br_if 0,
                    Wasm.Instr.i32_const 12,
                    Wasm.Instr.i32_const 1049084,
                    Wasm.Instr.i32_const 18,
                    Wasm.Instr.call 736,
                    Wasm.Instr.local_set 4,
                    Wasm.Instr.local_get 0,
                    Wasm.Instr.i32_const 1,
                    Wasm.Instr.store (Wasm.NumType.i32) none { align := 2, offset := 0 },
                    Wasm.Instr.local_get 0,
                    Wasm.Instr.local_get 4,
                    Wasm.Instr.store (Wasm.NumType.i64) none { align := 2, offset := 4 },
                    Wasm.Instr.local_get 3,
                    Wasm.Instr.i32_const 40,
                    Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                    Wasm.Instr.call 68,
                    Wasm.Instr.br 2],
                 Wasm.Instr.local_get 0,
                 Wasm.Instr.i32_const 8,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.local_get 3,
                 Wasm.Instr.i32_const 16,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.i32_const 40,
                 Wasm.Instr.call 951,
                 Wasm.Instr.drop,
                 Wasm.Instr.local_get 0,
                 Wasm.Instr.i32_const 0,
                 Wasm.Instr.store (Wasm.NumType.i32) none { align := 2, offset := 0 },
                 Wasm.Instr.br 1],
              Wasm.Instr.local_get 4,
              Wasm.Instr.call 760,
              Wasm.Instr.local_set 4,
              Wasm.Instr.local_get 0,
              Wasm.Instr.i32_const 1,
              Wasm.Instr.store (Wasm.NumType.i32) none { align := 2, offset := 0 },
              Wasm.Instr.local_get 0,
              Wasm.Instr.local_get 4,
              Wasm.Instr.store (Wasm.NumType.i64) none { align := 2, offset := 4 }],
           Wasm.Instr.local_get 3,
           Wasm.Instr.i32_const 144,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.global_set 0],
  bodySize := 254 }
def body : Expr := function.body
def signature : FuncType := {params:=[.num .i32,.num .i32,.num .i32],results:=[]}

private def blockBody (instruction : Instr) : Expr := match instruction with
  | .block _ body=>body
  | _=>[]

def setup : Expr := body.take 5
def saveSlice : Expr := (body.drop 5).take 6
def invokeWrapper : Expr := (body.drop 11).take 7
def cacheResult : Expr := (body.drop 18).take 6
def copyScratch : Expr := (body.drop 24).take 9
def outerBody : Expr := blockBody body[33]!
def acceptedBody : Expr := blockBody outerBody[0]!
def rejected : Expr := outerBody.drop 1
def restore : Expr := body.drop 34

def tagGuard : Expr := acceptedBody.take 4
def saveUpper : Expr := (acceptedBody.drop 4).take 5
-- The destination is ((R+16)|||4), exactly as deployed; no alignment is assumed.
def copyAccepted : Expr := (acceptedBody.drop 9).take 11
def exhaustionBody : Expr := blockBody acceptedBody[20]!
def exhaustionGuard : Expr := exhaustionBody.take 4
def trailingBytesRejected : Expr := exhaustionBody.drop 4
def copyResult : Expr := (acceptedBody.drop 21).take 9
def tagSuccess : Expr := (acceptedBody.drop 30).take 3

theorem body_segments : body=setup++saveSlice++invokeWrapper++cacheResult++copyScratch++
    [.block .empty ([.block .empty acceptedBody]++rejected)]++restore:=by kernel_rfl
theorem accepted_segments : acceptedBody=tagGuard++saveUpper++copyAccepted++
    [.block .empty exhaustionBody]++copyResult++tagSuccess++[.br 1]:=by kernel_rfl
theorem exhaustion_segments : exhaustionBody=exhaustionGuard++trailingBytesRejected:=by kernel_rfl

/-- Static success recipe, retaining both accepted branch guards. This is not
an execution theorem; all three actual free block entries remain in body. -/
def acceptedRecipe : Expr :=setup++saveSlice++invokeWrapper++cacheResult++copyScratch++
  tagGuard++saveUpper++copyAccepted++exhaustionGuard++copyResult++tagSuccess++[.br 1]++restore

theorem accepted_calls : acceptedRecipe.filterMap (fun i=>match i with|.call n=>some n|_=>none)=[162,951,951,951]:=by kernel_rfl
theorem accepted_recipe_length : acceptedRecipe.length=74:=by kernel_rfl
theorem first_copy_length : copyScratch.length=9:=by kernel_rfl
theorem second_copy_length : copyAccepted.length=11:=by kernel_rfl
theorem final_copy_length : copyResult.length=9:=by kernel_rfl

theorem module_function : wNearModule.funcs[113]?=some function:=by kernel_rfl
theorem module_signature : wNearModule.types[31]?=some signature:=by kernel_rfl
theorem activation_cost(op:Nat)(out pointer length:UInt32):
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 pointer,.i32 length])=11*op:=by
  simp[activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.StateDecodeBorshRead
