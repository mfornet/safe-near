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

theorem mstep_instr_trap (σ : Store NearState) (lim : ExecLimits) (C : Ctx) (f : Frame)
    (vs : List Value) (L : List Label) (i : Instr) (R : List Instr)
    (hmi : σ.modules[f.inst]? = some f.mi) {σ' : Store NearState} {r : Trap}
    (h : Exec.instr σ f.mi f.locals (C.base ++ vs).toArray L i R = ⟨σ', .trap r⟩) :
    Exec.step { store := σ, thread := C.thread f vs L (i :: R), limits := lim } = .trap r σ' := by
  simp [Exec.step, Ctx.thread, Ctx.threadA, modules_get! hmi, h]

/-- An instruction that traps without touching the store. -/
theorem mwpi_pure_trap (i : Instr) (hi : isFlat i = true) (r : Trap)
    (h : ∀ σ : Store NearState, ∀ base L R,
      Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R = ⟨σ, .trap r⟩) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ Φ.trap ⊢ mwpi cfg lim d f vs [i] Φ := by
  iintro ⟨Hc, HΦ⟩
  unfold mwpi mKont
  iintro %Ψ %C %hC #Hi HK
  have hmi : ∀ σ : Store NearState, (∀ p ∈ [((Loc.inst f.inst, Cell.inst f.mi) : Loc × Cell NearState)],
      lookup σ p.1 = some p.2) → σ.modules[f.inst]? = some f.mi := by
    intro σ hσ
    have := hσ _ List.mem_cons_self
    simp only [lookup_inst, Option.map_eq_some_iff] at this
    obtain ⟨m, hm, he⟩ := this
    cases he; exact hm
  have hRd' : ∀ p ∈ [((Loc.inst f.inst, Cell.inst f.mi) : Loc × Cell NearState)], isPlain p.1 := by
    intro p hp
    simp at hp; subst hp
    unfold isPlain; simp
  iapply mwp_lift_plain cfg lim (C.thread f vs C.labels ([i] ++ C.rest))
    [(Loc.inst f.inst, .inst f.mi)] [] (fun _ => [])
    (fun _ => .finished (.trap r))
    cfg.regularOpCost Cg R hRd' (by simp) (by simp) List.nodup_nil (fun _ => List.nodup_nil)
  · intro σ hR hPs
    have hx := h σ C.base C.labels C.rest
    rw [List.singleton_append, mstep_instr_trap σ lim C f vs C.labels i C.rest (hmi σ hR) hx,
      nextInstructionGas_flat cfg σ lim C f vs C.labels i C.rest hi]
    refine ⟨?_, rfl, rfl, fun l _ => ?_⟩
    · simp [frameTransitionGas]
    · rfl
  · intro σ hR hPs l hl hnone
    simp at hl
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    isplitr
    · iexact Hi
    · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro %σ %_ _ _
  icases HK with ⟨-, -, -, HK⟩
  iapply mwp_finished
  ispecialize HK $$ HΦ
  ispecialize HK $$ %r
  iexact HK

theorem mwpi_unreachable :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ Φ.trap ⊢ mwpi cfg lim d f vs [.unreachable] Φ :=
  mwpi_pure_trap _ rfl .unreachable fun _ _ _ _ => rfl

theorem mwpi_select_true (t : Option (List ValType)) (a b : Value) (c : UInt32) (hc : c ≠ 0) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [a]) f)
      ⊢ mwpi cfg lim d f (vs ++ [a, b, .i32 c]) [.select t] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32, hc]

theorem mwpi_select_false (t : Option (List ValType)) (a b : Value) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [b]) f)
      ⊢ mwpi cfg lim d f (vs ++ [a, b, .i32 0]) [.select t] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32]

theorem mwpi_ref_null (t : RefType) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [.ref (.null t)]) f)
      ⊢ mwpi cfg lim d f vs [.ref_null t] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_ref_is_null (r : Ref) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗
        Φ.normal (vs ++ [.i32 (Numeric.bool (match r with | .null _ => true | _ => false))]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.ref r]) [.ref_is_null] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by cases r <;> simp [Exec.instr]

theorem mwpi_ref_func (i : Nat) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.ref (.func f.mi.funcAddrs[i]!)]) f)
      ⊢ mwpi cfg lim d f vs [.ref_func i] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_f32_const (n : UInt32) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [.f32 n]) f)
      ⊢ mwpi cfg lim d f vs [.f32_const n] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_f64_const (n : UInt64) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [.f64 n]) f)
      ⊢ mwpi cfg lim d f vs [.f64_const n] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_i32_eqz (a : UInt32) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 (Numeric.bool (a == 0))]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i32 a]) [.i32_eqz] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32]

theorem mwpi_i64_eqz (a : UInt64) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 (Numeric.bool (a == 0))]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i64 a]) [.i64_eqz] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_i32_unop (op : IUnOp) (a : UInt32) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 (Numeric.iunop32 op a)]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i32 a]) [.i32_unop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32]

theorem mwpi_i64_unop (op : IUnOp) (a : UInt64) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i64 (Numeric.iunop64 op a)]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i64 a]) [.i64_unop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_i32_binop (op : IBinOp) (a b r : UInt32) (h : Numeric.ibinop32 op a b = .ok r) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 r]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i32 a, .i32 b]) [.i32_binop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32, h]

theorem mwpi_i32_binop_trap (op : IBinOp) (a b : UInt32) (t : Trap)
    (h : Numeric.ibinop32 op a b = .error t) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ Φ.trap
      ⊢ mwpi cfg lim d f (vs ++ [.i32 a, .i32 b]) [.i32_binop op] Φ :=
  mwpi_pure_trap _ rfl t fun _ _ _ _ => by simp [Exec.instr, Exec.i32, h]

theorem mwpi_i64_binop (op : IBinOp) (a b r : UInt64) (h : Numeric.ibinop64 op a b = .ok r) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i64 r]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i64 a, .i64 b]) [.i64_binop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, h]

theorem mwpi_i64_binop_trap (op : IBinOp) (a b : UInt64) (t : Trap)
    (h : Numeric.ibinop64 op a b = .error t) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ Φ.trap
      ⊢ mwpi cfg lim d f (vs ++ [.i64 a, .i64 b]) [.i64_binop op] Φ :=
  mwpi_pure_trap _ rfl t fun _ _ _ _ => by simp [Exec.instr, h]

theorem mwpi_i32_relop (op : IRelOp) (a b : UInt32) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 (Numeric.bool (Numeric.irelop32 op a b))]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i32 a, .i32 b]) [.i32_relop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, Exec.i32]

theorem mwpi_i64_relop (op : IRelOp) (a b : UInt64) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 (Numeric.bool (Numeric.irelop64 op a b))]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i64 a, .i64 b]) [.i64_relop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_f32_unop (op : FUnOp) (a : UInt32) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.f32 (Numeric.funop32 op a)]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.f32 a]) [.f32_unop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_f64_unop (op : FUnOp) (a : UInt64) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.f64 (Numeric.funop64 op a)]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.f64 a]) [.f64_unop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_f32_binop (op : FBinOp) (a b : UInt32) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.f32 (Numeric.fbinop32 op a b)]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.f32 a, .f32 b]) [.f32_binop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_f64_binop (op : FBinOp) (a b : UInt64) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.f64 (Numeric.fbinop64 op a b)]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.f64 a, .f64 b]) [.f64_binop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_f32_relop (op : FRelOp) (a b : UInt32) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 (Numeric.bool (Numeric.frelop32 op a b))]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.f32 a, .f32 b]) [.f32_relop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_f64_relop (op : FRelOp) (a b : UInt64) :
    credits Cg (cfg.regularOpCost + R) ∗
      ▷ (credits Cg R -∗ Φ.normal (vs ++ [.i32 (Numeric.bool (Numeric.frelop64 op a b))]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.f64 a, .f64 b]) [.f64_relop op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr]

theorem mwpi_cvt (op : CvtOp) (a r : Value) (h : Numeric.cvt op a = .ok r) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal (vs ++ [r]) f)
      ⊢ mwpi cfg lim d f (vs ++ [a]) [.cvt op] Φ :=
  mpure_same _ rfl _ fun _ _ _ _ => by simp [Exec.instr, h]

theorem mwpi_cvt_trap (op : CvtOp) (a : Value) (t : Trap) (h : Numeric.cvt op a = .error t) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ Φ.trap
      ⊢ mwpi cfg lim d f (vs ++ [a]) [.cvt op] Φ :=
  mwpi_pure_trap _ rfl t fun _ _ _ _ => by simp [Exec.instr, h]

end NearLogic
