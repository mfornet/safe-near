import Wasm.Validate

/-! Instruction validation depends on memory presence, not declared page
limits. Equal memory counts suffice for every body and constant expression.
This is a structural theorem, without assumptions about a body validator's
result or any execution. Module-level memory-limit checks remain separate. -/
namespace Wasm.Validate

theorem instr_seq_mems (ctx : Context) (mems : Array MemType)
    (hsize : mems.size = ctx.mems.size) :
    (∀ i, instr {ctx with mems} i = instr ctx i) ∧
    (∀ code, seq {ctx with mems} code = seq ctx code) := by
  apply instr.mutual_induct ctx
  all_goals intros
  all_goals simp_all only [instr, seq, blockFuncType, checkMultiValue, checkRefFeature,
    checkBulkFeature, funcType, tableType, globalType, localType, requireMemory]

theorem instr_mems (ctx : Context) (mems : Array MemType)
    (hsize : mems.size = ctx.mems.size) (i : Instr) :
    instr {ctx with mems} i = instr ctx i := (instr_seq_mems ctx mems hsize).1 i

theorem seq_mems (ctx : Context) (mems : Array MemType)
    (hsize : mems.size = ctx.mems.size) (code : Expr) :
    seq {ctx with mems} code = seq ctx code := (instr_seq_mems ctx mems hsize).2 code

theorem body_mems (ctx : Context) (mems : Array MemType)
    (hsize : mems.size = ctx.mems.size) (results : List ValType) (code : Expr) :
    body {ctx with mems} results code = body ctx results code := by
  simp only [body, seq_mems ctx mems hsize]

/-- Constant-instruction restrictions do not inspect memories at all. -/
theorem constInstr_mems (imported visible : Nat) (ctx : Context) (mems : Array MemType) :
    constInstr imported visible {ctx with mems} = constInstr imported visible ctx := by
  funext i
  cases i <;> rfl

theorem constExpr_mems (imported visible : Nat) (ctx : Context) (mems : Array MemType)
    (hsize : mems.size = ctx.mems.size) (type : ValType) (code : Expr) :
    constExpr imported visible {ctx with mems} type code = constExpr imported visible ctx type code := by
  simp only [constExpr, constInstr_mems, seq_mems ctx mems hsize]

/-- The configurable page bounds used by preparation satisfy the actual
memory-type checker under the protocol's explicit scalar inequalities. -/
theorem memTypeOk_of_bounds (min max : Nat) (horder : min ≤ max) (hmax : max ≤ 65536) :
    memTypeOk {limits := {min, max := some max}} = .ok () := by
  have hmin : ¬min > 65536 := by omega
  have hmax' : ¬max > 65536 := by omega
  have horder' : ¬max < min := by omega
  simp [memTypeOk, limitsOk, hmin, hmax', horder']
  rfl

end Wasm.Validate
