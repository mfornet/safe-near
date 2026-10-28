import Binary.StateDecodeBorsh

/-! Exact deployed162 Borsh result wrapper. Metadata and literal equality only;
its accepted425/copy composition is a separate execution proof. -/
namespace WNear.Binary.StateDecodeBorshWrapper
open Wasm Wasm.Near

def function : Func := {
  type := 14,
  locals := [Wasm.ValType.num (Wasm.NumType.i32),
             Wasm.ValType.num (Wasm.NumType.i64),
             Wasm.ValType.num (Wasm.NumType.i32)],
  body := [Wasm.Instr.global_get 0,
           Wasm.Instr.i32_const 96,
           Wasm.Instr.i32_binop (Wasm.IBinOp.sub),
           Wasm.Instr.local_tee 2,
           Wasm.Instr.global_set 0,
           Wasm.Instr.local_get 2,
           Wasm.Instr.i32_const 48,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.local_get 1,
           Wasm.Instr.call 425,
           Wasm.Instr.local_get 2,
           Wasm.Instr.load (Wasm.NumType.i64) none { align := 2, offset := 52 },
           Wasm.Instr.local_set 3,
           Wasm.Instr.local_get 2,
           Wasm.Instr.load (Wasm.NumType.i32) none { align := 2, offset := 48 },
           Wasm.Instr.local_set 4,
           Wasm.Instr.local_get 2,
           Wasm.Instr.i32_const 12,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.local_get 2,
           Wasm.Instr.i32_const 48,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.i32_const 12,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.i32_const 36,
           Wasm.Instr.call 951,
           Wasm.Instr.drop,
           Wasm.Instr.i32_const 1,
           Wasm.Instr.local_set 1,
           Wasm.Instr.block
             (Wasm.BlockType.empty)
             [Wasm.Instr.block
                (Wasm.BlockType.empty)
                [Wasm.Instr.local_get 4,
                 Wasm.Instr.i32_const 1,
                 Wasm.Instr.i32_relop (Wasm.IRelOp.eq),
                 Wasm.Instr.br_if 0,
                 Wasm.Instr.local_get 0,
                 Wasm.Instr.i32_const 8,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.local_get 3,
                 Wasm.Instr.i64_const 32,
                 Wasm.Instr.i64_binop (Wasm.IBinOp.shr_u),
                 Wasm.Instr.store (Wasm.NumType.i64) (some 32) { align := 2, offset := 0 },
                 Wasm.Instr.local_get 0,
                 Wasm.Instr.i32_const 12,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.local_get 2,
                 Wasm.Instr.i32_const 12,
                 Wasm.Instr.i32_binop (Wasm.IBinOp.add),
                 Wasm.Instr.i32_const 36,
                 Wasm.Instr.call 951,
                 Wasm.Instr.drop,
                 Wasm.Instr.i32_const 0,
                 Wasm.Instr.local_set 1,
                 Wasm.Instr.br 1],
              Wasm.Instr.local_get 0,
              Wasm.Instr.local_get 3,
              Wasm.Instr.call 760,
              Wasm.Instr.store (Wasm.NumType.i64) none { align := 2, offset := 4 }],
           Wasm.Instr.local_get 0,
           Wasm.Instr.local_get 1,
           Wasm.Instr.store (Wasm.NumType.i32) none { align := 2, offset := 0 },
           Wasm.Instr.local_get 2,
           Wasm.Instr.i32_const 96,
           Wasm.Instr.i32_binop (Wasm.IBinOp.add),
           Wasm.Instr.global_set 0],
  bodySize := 162 }
def body : Expr := function.body
def signature : FuncType := {params:=[.num .i32,.num .i32],results:=[]}
theorem exact_function : WNear.Binary.f162=function:=by kernel_rfl
theorem module_function : wNearModule.funcs[114]?=some function:=by kernel_rfl
theorem module_signature : wNearModule.types[14]?=some signature:=by kernel_rfl
theorem activation_cost(op:Nat)(out slice:UInt32):
    activationGas op (MeteredLogic.wasmLocals function [.i32 out,.i32 slice])=11*op:=by
  simp[activationGas,MeteredLogic.wasmLocals,function,ValType.default]
end WNear.Binary.StateDecodeBorshWrapper
