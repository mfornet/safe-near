import Bridge.Functions.AllocNewCell

/-!
# `memory.grow` against the memory's limit, and 577 with it (milestone M4)

`AllocGrow.mwpi_memory_grow_either` does not see the memory's declared maximum, so both of
its branches must be proved and neither says *why* it happens. Owning the (persistent)
limit `n ↪[wmlimit] some maxP` decides it:

* `mwpi_memory_grow_lim`: the success branch is entered with `GrowOk len (some maxP) k`
  (`len / 65536 + k ≤ 65536` and `≤ maxP`), the failure branch with its negation.
* `f577_lim`: `new_cell_for_free_list` (577) as `AllocNewCell.f577_spec`, same cost, the
  limit held, its failure branch carrying `¬ GrowOk len (some maxP) (cellPages w al)`
  (`postL`).
* `growOk_of_room`: under `len + P · 65536 + 65536 ≤ 2^32` and `(len + P · 65536) / 65536 ≤
  maxP`, `GrowOk` holds, so the failure branch is unreachable.
-/

namespace WNear.Binary.AllocLimit

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.AllocLeaves WNear.Binary.AllocGrow WNear.Binary.AllocNewCell
open WNear.Binary.U128From (memBytes_split memBytes_join)

theorem growOk_of_room (len P maxP : Nat) (h0 : len % 65536 = 0) (h1 : len + P * 65536 + 65536 ≤ 2 ^ 32)
    (h2 : (len + P * 65536) / 65536 ≤ maxP) : GrowOk len (some maxP) P := by
  refine ⟨?_, ?_⟩
  · simp only [pageSize, maxPages]; omega
  · intro m hm; cases hm; simp only [pageSize]; omega

section Rule

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg R : Nat}

open Classical in
/-- `memory.grow` by `k` pages, metered, holding the memory's limit: the new pages when
`GrowOk len (some maxP) k`, `-1` otherwise; `linear_op_base_cost + linear_op_unit_cost * k`
either way. -/
theorem mwpi_memory_grow_lim (n len maxP : Nat) (k : UInt32) (hn : f.mi.memAddrs[0]? = some n) :
    credits Cg (cfg.linearOpBaseCost + cfg.linearOpUnitCost * k.toNat + R) ∗ n ↦[wmlength] len ∗
      n ↪[wmlimit] some maxP ∗
      ▷ ((⌜GrowOk len (some maxP) k.toNat⌝ -∗ ∀ bs : List UInt8,
            ⌜bs = List.replicate (k.toNat * pageSize) 0⌝ -∗
            n ↦[wmlength] (len + k.toNat * pageSize) -∗ n ↦[wms][ len ] bs -∗ credits Cg R -∗
          Φ.normal (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f) ∧
        (⌜¬ GrowOk len (some maxP) k.toNat⌝ -∗ n ↦[wmlength] len -∗ credits Cg R -∗
          Φ.normal (vs ++ [.i32 0xFFFFFFFF]) f))
      ⊢ mwpi cfg lim d f (vs ++ [.i32 k]) [.memory_grow] Φ := by
  let ok : Prop := GrowOk len (some maxP) k.toNat
  unfold mwpi mKont
  iintro ⟨Hc, Hl, #Hm, HΦ⟩ %Ψ %C %hC #Hi HK
  have hmi : ∀ σ : Store NearState, (∀ p ∈ [(Loc.inst f.inst, Cell.inst f.mi),
      (Loc.memLimit n, (Cell.memLimit (some maxP) : Cell NearState))],
      lookup σ p.1 = some p.2) → σ.modules[f.inst]? = some f.mi := by
    intro σ hσ
    have := hσ _ List.mem_cons_self
    simp only [lookup_inst, Option.map_eq_some_iff] at this
    obtain ⟨m, hm, he⟩ := this
    cases he; exact hm
  have hRd : ∀ p ∈ [(Loc.inst f.inst, (Cell.inst f.mi : Cell NearState)),
      (Loc.memLimit n, (Cell.memLimit (some maxP) : Cell NearState))], isPlain p.1 := by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> (unfold isPlain; simp)
  have hPp : ∀ p ∈ [(Loc.memLength n, (Cell.memLength len : Cell NearState))], isPlain p.1 := by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp
    simp [isPlain, Loc.memLength]
  iapply mwp_lift_plain cfg lim (C.thread f (vs ++ [.i32 k]) C.labels ([.memory_grow] ++ C.rest))
    [(Loc.inst f.inst, .inst f.mi), (Loc.memLimit n, .memLimit (some maxP))]
    [(Loc.memLength n, .memLength len)]
    (fun _ => if ok then growCells n len k.toNat else [(Loc.memLength n, .memLength len)])
    (fun _ => .running cfg lim (C.thread f (if ok then vs ++ [.i32 (UInt32.ofNat (len / pageSize))]
      else vs ++ [.i32 0xFFFFFFFF]) C.labels C.rest))
    (cfg.linearOpBaseCost + cfg.linearOpUnitCost * k.toNat) Cg R hRd hPp
    (fun σ => by split <;> [exact growCells_plain _ _ _; exact hPp]) (by simp)
    (fun σ => by split <;> simp [growCells_nodup])
  · intro σ hR hP
    obtain ⟨mem, hmem, hwf, hlen⟩ := memLength_facts (hP _ List.mem_cons_self)
    obtain ⟨mem', hmem', hmax⟩ := memLimit_facts (hR _ (List.mem_cons_of_mem _ List.mem_cons_self))
    rw [hmem] at hmem'; cases hmem'
    have hm := hmi σ hR
    rw [List.singleton_append]
    by_cases hok : ok
    · simp only [hok, ite_true]
      have hok' : GrowOk len mem.max k.toNat := by rw [hmax]; exact hok
      obtain ⟨σ', hinstr, hrep⟩ := grow_step_ok hn hmem hwf hlen k hok' f.locals (C.base ++ vs)
        C.labels C.rest
      have hhost : σ'.host = σ.host := by
        have h2 := congrArg (fun r => r.1.host) hinstr
        simp [Exec.instr, Exec.i32, memOf_eq hn hmem, Store.setMemOf] at h2
        rw [grow_eq (by rw [hlen]; exact hok')] at h2
        simp [hn] at h2
        exact h2.symm
      simp only [List.append_assoc] at hinstr
      have hstep := step_instr_continue σ lim C f _ C.labels _ C.rest hm hinstr
      rw [hstep, nextInstructionGas_grow,
        frameTransitionGas_same cfg _ _ (by simp [Config.callDepth, Ctx.thread, Ctx.threadA])]
      refine ⟨rfl, ?_, hhost, fun l _ => hrep l⟩
      rfl
    · simp only [hok, ite_false]
      have hok' : ¬ GrowOk len mem.max k.toNat := by rw [hmax]; exact hok
      have hinstr := grow_step_fail hn hmem hlen k hok' f.locals (C.base ++ vs) C.labels C.rest
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
    iapply (seeList_cons _ _).2
    iunfold memLimit at Hm
    isplitr
    · iexact Hm
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
  by_cases hok : ok
  · simp only [hok, ite_true, growCells]
    icases HΦ with ⟨HΦ, -⟩
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ1, HQ2⟩
    ispecialize HK $$ %_ %f.locals
    simp only [Frame.withLocals_self]
    iapply HK
    iapply HΦ $$ %hok %_ %rfl [HQ1] [HQ2] Hc
    · iunfold memLength; iexact HQ1
    · iunfold WasmLogic.memBytes; iexact HQ2
  · simp only [hok, ite_false]
    icases HΦ with ⟨-, HΦ⟩
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    ispecialize HK $$ %_ %f.locals
    simp only [Frame.withLocals_self]
    iapply HK
    iapply HΦ $$ %hok [HQ] Hc
    iunfold memLength; iexact HQ

end Rule

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `AllocNewCell.post` with the reason of a failure: the limit forbids the grow. -/
def postL (n : Nat) (out sw al : UInt32) (len maxP : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗
    ((n ↦[wms][ out.toNat ] bytes32 0 ∗ n ↦[wms][ out.toNat + 4 ] bytes32 (UInt32.ofNat len) ∗
      n ↦[wmlength] (len + (cellPages sw al).toNat * pageSize) ∗
      n ↦[wms][ len ] bytes32 ((UInt32.ofNat len + cellPages sw al <<< 16) ||| 2) ∗
      n ↦[wms][ len + 4 ] List.drop 4 (storeBytes (.i64 0) 8) ∗ n ↦[wms][ len + 8 ] bytes32 0 ∗
      ∃ rest : List UInt8, ⌜rest.length = (cellPages sw al).toNat * 65536 - 12 ∧ ∀ x ∈ rest, x = 0⌝ ∗
        n ↦[wms][ len + 12 ] rest) ∨
     (⌜¬ GrowOk len (some maxP) (cellPages sw al).toNat⌝ ∗
      n ↦[wms][ out.toNat ] bytes32 1 ∗ n ↦[wms][ out.toNat + 4 ] bytes32 4294967295 ∗
      n ↦[wmlength] len)))

set_option maxHeartbeats 2000000 in
/-- 577 holding the memory's limit: `AllocNewCell.f577_spec` whose failure says why. -/
theorem f577_lim (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n)
    (a572 a569 a568 a573 a574 : Nat)
    (h572 : mi.funcAddrs[572]? = some a572) (h569 : mi.funcAddrs[569]? = some a569)
    (h568 : mi.funcAddrs[568]? = some a568) (h573 : mi.funcAddrs[573]? = some a573)
    (h574 : mi.funcAddrs[574]? = some a574)
    (ty572 ty569 ty568 ty573 ty574 : FuncType)
    (hp572 : ty572.params.length = 1) (hr572 : ty572.results.length = 1)
    (hp569 : ty569.params.length = 1) (hr569 : ty569.results.length = 1)
    (hp568 : ty568.params.length = 2) (hr568 : ty568.results.length = 1)
    (hp573 : ty573.params.length = 1) (hr573 : ty573.results.length = 1)
    (hp574 : ty574.params.length = 1) (hr574 : ty574.results.length = 0)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (out pol sw al : UInt32) (len maxP : Nat) (o1 o2 : List UInt8)
    (hsw : sw.toNat < 2 ^ 29) (hal : al.toNat < 2 ^ 20)
    (hout : out.toNat + 8 ≤ 2 ^ 32) (hlen0 : len % 65536 = 0) (ho1 : o1.length = 4) (ho2 : o2.length = 4) :
    n ↪[wmlimit] some maxP ∗
      a572 ↪[wf] FuncInst.wasm ty572 inst f572 ∗ a569 ↪[wf] FuncInst.wasm ty569 inst f569 ∗
      a568 ↪[wf] FuncInst.wasm ty568 inst f568 ∗ a573 ↪[wf] FuncInst.wasm ty573 inst f573 ∗
      a574 ↪[wf] FuncInst.wasm ty574 inst f574 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f577 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 pol, .i32 sw, .i32 al]⌝ ∗
          n ↦[wms][ out.toNat ] o1 ∗ n ↦[wms][ out.toNat + 4 ] o2 ∗ n ↦[wmlength] len))
        (fun _ => 166 * cfg.regularOpCost + cfg.linearOpBaseCost +
          cfg.linearOpUnitCost * (cellPages sw al).toNat)
        (postL n out sw al len maxP) := by
  iintro ⟨#Hm, #H572, #H569, #H568, #H573, #H574, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Ho1, Ho2, Hl⟩ Hc
  subst hargs
  simp only [f577]
  mstep
  mcall (f572_spec cfg lim (d + 1) ty572 hr572 inst mi Cg sw (by omega))
    with (simp [activationGas, entryLocals, f572, ValType.default, hp572]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep
  mstep_not_taken with ucond
  mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (simp [and_mask_eq (al + 64) 536870911 29 (by decide) (by simp; omega), Numeric.bool, Numeric.irelop32])
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply mwpi_select_ite
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨rfl, by omega⟩
  inext
  iintro Hc
  rw [select_gt]
  mctrl_norm
  rw [show (if (al + 64) <<< (3 % 32) < sw <<< 2 then sw <<< 2 else (al + 64) <<< (3 % 32)) = cellBytes sw al from rfl]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (have := cellBytes_toNat sw al hsw hal; ucond)
  mstep; mstep; mstep
  mcall (f569_spec cfg lim (d + 1) ty569 hr569 inst mi a568 h568 ty568 hp568 hr568 (by omega) Cg
      (cellBytes sw al + 8) (by have := cellBytes_toNat sw al hsw hal; rw [UInt32.toNat_add]; simp; omega))
    with (simp [activationGas, entryLocals, f569, ValType.default, hp569]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep
  rw [show (cellBytes sw al + 8 + 65536 + 4294967295) / 65536 = cellPages sw al from rfl]
  rw [show 166 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages sw al).toNat + R -
      93 * cfg.regularOpCost = cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages sw al).toNat +
      (73 * cfg.regularOpCost + R) by omega]
  iapply mwpi_cons
  rw [show [Value.i32 (cellPages sw al)] = [] ++ [Value.i32 (cellPages sw al)] from rfl]
  iapply (mwpi_memory_grow_lim (vs := []) n len maxP (cellPages sw al) hn)
  isplitl [Hc]
  · iexact Hc
  isplitl [Hl]
  · iexact Hl
  isplitr
  · iexact Hm
  inext
  isplit
  · iintro %hok %bs %hbs Hl Hnew Hc
    simp only [Post.mseq_normal, List.nil_append]
    have hkb := cellPages_bounds sw al hsw hal
    have hpg : len / 65536 < 65536 := by have := hok.1; simp [pageSize, maxPages] at this; omega
    clear hok
    mstep; mstep; mstep
    mstep_taken with (exact ne_neg1 _ hpg)
    mstep; mstep; mstep; mstep; mstep
    mstep_not_taken with (exact mask_ne _ hpg)
    mstep
    mcall (f573_spec cfg lim (d + 1) ty573 hr573 inst mi Cg (cellPages sw al) hkb.2)
      with (simp [activationGas, entryLocals, f573, ValType.default, hp573]; omega)
    · ipureintro; trivial
    icases HQ with %hrs
    subst hrs
    mstep
    mcall (f574_spec cfg lim (d + 1) ty574 hr574 inst mi Cg (cellPages sw al <<< 16)
        (by rw [shl16_toNat _ hkb.2]; omega))
      with (simp [activationGas, entryLocals, f574, ValType.default, hp574]; omega)
    · ipureintro; trivial
    icases HQ with %hrs
    subst hrs
    have hbl : bs.length = (cellPages sw al).toNat * 65536 := by rw [hbs]; simp [pageSize]
    have hz : ∀ x ∈ bs, x = 0 := by rw [hbs]; intro x hx; exact List.eq_of_mem_replicate hx
    clear hbs
    icases memBytes_split n len 8 bs (by omega) $$ Hnew with ⟨H8, Hr⟩
    icases memBytes_split n (len + 8) 4 (bs.drop 8) (by simp; omega) $$ Hr with ⟨H4, Hr⟩
    have hX : UInt32.ofNat (len / pageSize) <<< (16 % 32) = UInt32.ofNat len := by
      apply UInt32.toNat_inj.mp; rw [page_shl' len hlen0 hpg]; simp; omega
    mstep; mstep; mstep; mstep
    rw [hX]; clear hX
    mstep
    ihave H8 := memBytes_eq (take_zeros bs hz 8 (by omega)) $$ H8
    ihave H4 := memBytes_eq (take_zeros (bs.drop 8) (fun x hx => hz x (List.mem_of_mem_drop hx)) 4
      (by simp; omega)) $$ H4
    simp only [List.replicate]
    mstep [H8]
    mstep; mstep; mstep; mstep
    mstep [H4]
    icases memBytes_split n len 4 _ (by simp [storeBytes]) $$ H8 with ⟨H8a, H8b⟩
    mstep; mstep; mstep; mstep; mstep; mstep
    mstep [H8a]
    have hrest : (List.drop 4 (List.drop 8 bs)).length = (cellPages sw al).toNat * 65536 - 12 ∧
        ∀ x ∈ List.drop 4 (List.drop 8 bs), x = 0 :=
      ⟨by simp; omega, fun x hx => hz x (List.mem_of_mem_drop (List.mem_of_mem_drop hx))⟩
    ihave Hr : (∃ rest : List UInt8, ⌜rest.length = (cellPages sw al).toNat * 65536 - 12 ∧
        ∀ x ∈ rest, x = 0⌝ ∗ n ↦[wms][ len + 12 ] rest) $$ [Hr]
    · iexists _; iframe Hr; ipureintro; exact hrest
    clear hrest hz hbl
    mstep; mstep
    clear hpg hkb
    mstep [Ho2]; mstep; mstep; mstep [Ho1]; mstep
    iframe Hc
    iunfold postL
    isplitr; · ipureintro; rfl
    ileft
    iframe Ho1 Ho2 Hl H8a H8b H4 Hr
  · iintro %hfail Hl Hc
    clear hlen0 hsw hal
    simp only [Post.mseq_normal, List.nil_append]
    mstep; mstep; mstep
    mstep_not_taken with (simp [Numeric.bool, Numeric.irelop32])
    mstep; mstep; mstep
    mstep; mstep; mstep [Ho2]; mstep; mstep; mstep [Ho1]; mstep
    mcredits R
    iframe Hc
    iunfold postL
    isplitr; · ipureintro; rfl
    iright
    iframe Ho1 Ho2 Hl
    ipureintro; exact hfail

end Spec

end WNear.Binary.AllocLimit
