import NearLogic.Frag

/-!
# Rules for instructions that do not touch the store, metered

WasmLogic's pure rules (`WasmLogic/Rules/Pure.lean`), each for one
`regular_op_cost` of credits. Rules are added as proofs need them.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg R : Nat}

/-- A flat instruction that only moves operands and locals. -/
theorem mwpi_pure (i : Instr) (hi : isFlat i = true) (vs' : List Value) (loc' : Array Value)
    (h : ∀ σ : Store NearState, ∀ base L R, Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R =
      ⟨σ, .continue (base ++ vs').toArray L R loc'⟩) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal vs' (f.withLocals loc'))
      ⊢ mwpi cfg lim d f vs [i] Φ := by
  iintro ⟨Hc, HΦ⟩
  iapply mwpi_instr i hi vs' loc' [] [] [] (by simp) (by simp) (by simp) List.nodup_nil List.nodup_nil
  · intro σ _ _ _ base L R
    exact ⟨σ, h σ base L R, fun l => by simp, rfl⟩
  · intro σ _ _ _ l hl _
    simp at hl
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro _ Hc
  iapply HΦ $$ Hc

private theorem mpure_same (i : Instr) (hi : isFlat i = true) (vs' : List Value)
    (h : ∀ σ : Store NearState, ∀ base L R, Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R =
      ⟨σ, .continue (base ++ vs').toArray L R f.locals⟩) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal vs' f)
      ⊢ mwpi cfg lim d f vs [i] Φ := by
  have := mwpi_pure (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (Cg := Cg) (R := R) i hi vs' f.locals h
  simpa using this

theorem mwpi_nop :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal vs f)
      ⊢ mwpi cfg lim d f vs [.nop] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => rfl

theorem mwpi_drop (v : Value) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal vs f)
      ⊢ mwpi cfg lim d f (vs ++ [v]) [.drop] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_i32_const (n : UInt32) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 n]) f)
      ⊢ mwpi cfg lim d f vs [.i32_const n] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_i64_const (n : UInt64) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i64 n]) f)
      ⊢ mwpi cfg lim d f vs [.i64_const n] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_local_get (i : Nat) (v : Value) (h : f.locals[i]? = some v) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [v]) f)
      ⊢ mwpi cfg lim d f vs [.local_get i] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, getElem!_def, h]

theorem mwpi_local_set (i : Nat) (v : Value) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal vs (f.withLocals (f.locals.set! i v)))
      ⊢ mwpi cfg lim d f (vs ++ [v]) [.local_set i] Φ :=
  mwpi_pure _ rfl _ _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_local_tee (i : Nat) (v : Value) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [v]) (f.withLocals (f.locals.set! i v)))
      ⊢ mwpi cfg lim d f (vs ++ [v]) [.local_tee i] Φ :=
  mwpi_pure _ rfl _ _ fun _ _ _ _ => by simp [Exec.instr]

end NearLogic
