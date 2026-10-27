import NearLogic.Tactic.Control

/-!
# `memory.grow`, metered

NearLogic has no rule for `memory.grow` yet; wee_alloc's
`new_cell_for_free_list` (577) needs one. `memory.grow` is a *linear*
instruction: `nextInstructionGas` charges `linear_op_base_cost +
linear_op_unit_cost * k` for `k` pages (the operand on top of the stack),
whether or not the growth succeeds.

`mwpi_memory_grow_either` is WasmLogic's `wpi_memory_grow_either` for those
credits: owning the memory's length `n ↦[wmlength] len`, the instruction
either succeeds (then `len / 65536 + k ≤ maxPages`, the length is
`len + k * 65536` and the new bytes, all zero, are owned) and pushes the old
size in pages, or fails and pushes `-1` with nothing changed. Which branch
happens depends on the memory's declared maximum, which this rule does not
need to know (so both branches must be proved, as wee_alloc's code does).

The new bytes come as an abstract `bs` with the pure fact
`bs = List.replicate (k * 65536) 0`: a points-to on the `replicate` term itself,
with `k` symbolic, makes the kernel unfold `Nat.mul` 65536 deep.
-/

namespace WNear.Binary.AllocGrow

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

theorem nextInstructionGas_grow (cfg : WasmConfig) (σ : Store NearState) (lim : ExecLimits)
    (C : Ctx) (f : Frame) (vs : List Value) (L : List Label) (k : UInt32) (R : List Instr) :
    nextInstructionGas cfg
      (Config.mk σ (C.thread f (vs ++ [.i32 k]) L (.memory_grow :: R)) lim) = cfg.linearOpBaseCost + cfg.linearOpUnitCost * k.toNat := by
  simp [nextInstructionGas, Config.nextInstr?, Config.stackTop?, Ctx.thread, Ctx.threadA,
    linearInstruction]

theorem growCells_plain (n len k : Nat) : ∀ p ∈ growCells (H := NearState) n len k, isPlain p.1 := by
  intro p hp
  simp only [growCells, List.mem_cons] at hp
  rcases hp with rfl | hp
  · simp [isPlain, Loc.memLength]
  · exact byteCells_plain _ _ _ p hp

section Rule

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg R : Nat}

open Classical in
/-- `memory.grow` by `k` pages, metered: either `k` new pages of zeros and the
old size, or `-1`; `linear_op_base_cost + linear_op_unit_cost * k` either way. -/
theorem mwpi_memory_grow_either (n len : Nat) (k : UInt32) (hn : f.mi.memAddrs[0]? = some n) :
    credits Cg (cfg.linearOpBaseCost + cfg.linearOpUnitCost * k.toNat + R) ∗ n ↦[wmlength] len ∗
      ▷ ((⌜len / pageSize + k.toNat ≤ maxPages⌝ -∗ ∀ bs : List UInt8, ⌜bs = List.replicate (k.toNat * pageSize) 0⌝ -∗
            n ↦[wmlength] (len + k.toNat * pageSize) -∗ n ↦[wms][ len ] bs -∗ credits Cg R -∗
          Φ.normal (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f) ∧
        (n ↦[wmlength] len -∗ credits Cg R -∗ Φ.normal (vs ++ [.i32 0xFFFFFFFF]) f))
      ⊢ mwpi cfg lim d f (vs ++ [.i32 k]) [.memory_grow] Φ := by
  let ok : Store NearState → Prop := fun σ =>
    ∃ mem, σ.mems[n]? = some mem ∧ GrowOk len mem.max k.toNat
  unfold mwpi mKont
  iintro ⟨Hc, Hl, HΦ⟩ %Ψ %C %hC #Hi HK
  have hmi : ∀ σ : Store NearState, (∀ p ∈ [(Loc.inst f.inst, Cell.inst f.mi)],
      lookup σ p.1 = some p.2) → σ.modules[f.inst]? = some f.mi := by
    intro σ hσ
    have := hσ _ List.mem_cons_self
    simp only [lookup_inst, Option.map_eq_some_iff] at this
    obtain ⟨m, hm, he⟩ := this
    cases he; exact hm
  have hRd : ∀ p ∈ [(Loc.inst f.inst, (Cell.inst f.mi : Cell NearState))], isPlain p.1 := by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp
    unfold isPlain; simp
  have hPp : ∀ p ∈ [(Loc.memLength n, (Cell.memLength len : Cell NearState))], isPlain p.1 := by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp
    simp [isPlain, Loc.memLength]
  iapply mwp_lift_plain cfg lim (C.thread f (vs ++ [.i32 k]) C.labels ([.memory_grow] ++ C.rest))
    [(Loc.inst f.inst, .inst f.mi)] [(Loc.memLength n, .memLength len)]
    (fun σ => if ok σ then growCells n len k.toNat else [(Loc.memLength n, .memLength len)])
    (fun σ => .running cfg lim (C.thread f (if ok σ then vs ++ [.i32 (UInt32.ofNat (len / pageSize))]
      else vs ++ [.i32 0xFFFFFFFF]) C.labels C.rest))
    (cfg.linearOpBaseCost + cfg.linearOpUnitCost * k.toNat) Cg R hRd hPp
    (fun σ => by split <;> [exact growCells_plain _ _ _; exact hPp]) (by simp)
    (fun σ => by split <;> simp [growCells_nodup])
  · intro σ hR hP
    obtain ⟨mem, hmem, hwf, hlen⟩ := memLength_facts (hP _ List.mem_cons_self)
    have hm := hmi σ hR
    rw [List.singleton_append]
    by_cases hok : GrowOk len mem.max k.toNat
    · have hσ : ok σ := ⟨mem, hmem, hok⟩
      simp only [hσ, ite_true]
      obtain ⟨σ', hinstr, hrep⟩ := grow_step_ok hn hmem hwf hlen k hok f.locals (C.base ++ vs)
        C.labels C.rest
      have hhost : σ'.host = σ.host := by
        have h2 := congrArg (fun r => r.1.host) hinstr
        simp [Exec.instr, Exec.i32, memOf_eq hn hmem, Store.setMemOf] at h2
        rw [grow_eq (by rw [hlen]; exact hok)] at h2
        simp [hn] at h2
        exact h2.symm
      simp only [List.append_assoc] at hinstr
      have hstep := step_instr_continue σ lim C f _ C.labels _ C.rest hm hinstr
      rw [hstep, nextInstructionGas_grow,
        frameTransitionGas_same cfg _ _ (by simp [Config.callDepth, Ctx.thread, Ctx.threadA])]
      refine ⟨rfl, ?_, hhost, fun l _ => hrep l⟩
      rfl
    · have hσ : ¬ok σ := fun ⟨m, hm', h⟩ => by rw [hmem] at hm'; cases hm'; exact hok h
      simp only [hσ, ite_false]
      have hinstr := grow_step_fail hn hmem hlen k hok f.locals (C.base ++ vs) C.labels C.rest
      simp only [List.append_assoc] at hinstr
      rw [step_instr_continue σ lim C f _ C.labels _ C.rest hm hinstr,
        nextInstructionGas_grow, frameTransitionGas_same cfg _ _ (by simp [Config.callDepth, Ctx.thread, Ctx.threadA])]
      refine ⟨rfl, ?_, rfl, fun l _ => replaces_same hP l⟩
      rfl
  · intro σ _ hP l hq hp
    split at hq
    · exact grow_fresh (hP _ List.mem_cons_self) l hq hp
    · simp_all
  isplitl [Hc]
  · iexact Hc
  isplitl []
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    isplitr
    · iexact Hi
    · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hl]
  · iunfold memLength at Hl
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hl]
    · iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro %σ %_ HQ Hc
  icases HK with ⟨HK, -⟩
  by_cases hσ : ok σ
  · obtain ⟨_, _, hok⟩ := hσ
    have hσ' : ok σ := ⟨_, by assumption, hok⟩
    simp only [hσ', ite_true, growCells]
    icases HΦ with ⟨HΦ, -⟩
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ1, HQ2⟩
    ispecialize HK $$ %_ %f.locals
    simp only [Frame.withLocals_self]
    iapply HK
    iapply HΦ $$ %hok.1 %_ %rfl [HQ1] [HQ2] Hc
    · iunfold memLength; iexact HQ1
    · iunfold WasmLogic.memBytes; iexact HQ2
  · simp only [hσ, ite_false]
    icases HΦ with ⟨-, HΦ⟩
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    ispecialize HK $$ %_ %f.locals
    simp only [Frame.withLocals_self]
    iapply HK
    iapply HΦ $$ [HQ] Hc
    iunfold memLength; iexact HQ

end Rule

end WNear.Binary.AllocGrow
