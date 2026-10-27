import NearLogic.Call

/-!
# Calling a host function whose result host is described by a predicate

`ReadContractP` is `ReadContract` with the resulting host characterized by a
predicate `Q` instead of being fixed up to gas: the call returns some host
`host'` with `Q host'`. `mwp_lift_host_pred` generalizes `mwp_lift_host` to
such a step, and `mwpi_call_host_ro_pred` is the corresponding `call i`
rule, whose continuation receives the resulting host `h'` and `Q h'`.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-- A host function that reads the bytes `bs` at `ptr`, leaves memory alone,
and ends with a host satisfying `Q`. -/
def ReadContractP (fn : HostFn NearState) (h : NearState) (Q : NearState → Prop) (args rs : List Value)
    (ptr : Nat) (bs : List UInt8) (kh C : Nat) : Prop :=
  ∀ (host : NearState) (mem : Memory), mem.wf → erase host = erase h →
    (∀ k, k < bs.length → ptr + k < mem.byteSize ∧ mem.read8 (ptr + k) = bs[k]!) →
    host.gas.used + kh ≤ C → C ≤ host.gas.maxBurnt → C ≤ host.gas.prepaid →
    ∃ host', fn.call host (some mem) args = .return rs host' (some mem) ∧ Q host' ∧
      host'.gas.used ≤ host.gas.used + kh ∧ host'.gas.maxBurnt = host.gas.maxBurnt ∧
      host'.gas.prepaid = host.gas.prepaid

/-- A `ReadContract` is a `ReadContractP` for the predicate "equal to `h'` up to gas". -/
theorem ReadContract.toP {fn : HostFn NearState} {h h' : NearState} {args rs : List Value} {ptr : Nat}
    {bs : List UInt8} {kh C : Nat} (hc : ReadContract fn h h' args rs ptr bs kh C) :
    ReadContractP fn h (fun x => erase x = erase h') args rs ptr bs kh C := hc

/-- Weakening the predicate. -/
theorem ReadContractP.mono {fn : HostFn NearState} {h : NearState} {Q Q' : NearState → Prop}
    {args rs : List Value} {ptr : Nat} {bs : List UInt8} {kh C : Nat}
    (hc : ReadContractP fn h Q args rs ptr bs kh C) (hQ : ∀ x, Q x → Q' x) :
    ReadContractP fn h Q' args rs ptr bs kh C := by
  intro host mem hwf he hrd hu hmb hpp
  obtain ⟨host', h1, h2, h3⟩ := hc host mem hwf he hrd hu hmb hpp
  exact ⟨host', h1, hQ _ h2, h3⟩

section Host

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {s : Stuckness} {E : CoPset} {Φ : Ending → IProp GF}

/-- A step that calls a host function: from the host `h` (gas aside) it
leaves the host `h'`, touches the plain cells `P` as `Q`, enters no frame,
and the host function charges at most `kh` gas. It costs the instruction's
charge `k` and `kh`. Its facts are about `Exec.step` from any store with the
cells, the host and room for `kh` more gas. -/
theorem mwp_lift_host_pred (cfg : WasmConfig) (lim : ExecLimits) (t : Thread)
    (Rd P Q : List (Loc × Cell NearState)) (h : NearState) (Qh : NearState → Prop) (e' : MCode) (k kh C R : Nat)
    (hRd : ∀ p ∈ Rd, isPlain p.1) (hPp : ∀ p ∈ P, isPlain p.1) (hQp : ∀ p ∈ Q, isPlain p.1)
    (hP : (P.map (·.1)).Nodup) (hQ : (Q.map (·.1)).Nodup)
    (hk : ∀ σ : Store NearState, nextInstructionGas cfg { store := σ, thread := t, limits := lim } = k)
    (hstep : ∀ σ : Store NearState, (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) → erase σ.host = erase h →
      σ.host.gas.used + kh ≤ C → C ≤ σ.host.gas.maxBurnt → C ≤ σ.host.gas.prepaid →
      frameTransitionGas cfg { store := σ, thread := t, limits := lim }
          (Exec.step { store := σ, thread := t, limits := lim }) = 0 ∧
        ofMachine cfg lim (Exec.step { store := σ, thread := t, limits := lim }) = e' ∧
        Qh (Exec.step { store := σ, thread := t, limits := lim }).store.host ∧
        (Exec.step { store := σ, thread := t, limits := lim }).store.host.gas.used ≤ σ.host.gas.used + kh ∧
        (Exec.step { store := σ, thread := t, limits := lim }).store.host.gas.maxBurnt = σ.host.gas.maxBurnt ∧
        (Exec.step { store := σ, thread := t, limits := lim }).store.host.gas.prepaid = σ.host.gas.prepaid ∧
        ∀ l, isPlain l → lookup (Exec.step { store := σ, thread := t, limits := lim }).store l =
          (Q.lookup l).or (if (P.lookup l).isSome then none else lookup σ l))
    (hfresh : ∀ σ : Store NearState, (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      ∀ l, (Q.lookup l).isSome → P.lookup l = none → lookup σ l = none) :
    credits C (k + kh + R) ∗ mhostPt h ∗ seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗
      ▷ (∀ h', ⌜Qh h'⌝ -∗ mhostPt h' -∗ ([∗list] p ∈ Q, p.1 ↦ₛ p.2) -∗ credits C R -∗ WP e' @ s; E {{ Φ }})
      ⊢ WP (MCode.running cfg lim t) @ s; E {{ Φ }} := by
  iintro ⟨Hc, Hh, HRd, HP, Hwp⟩
  iunfold credits at Hc
  icases Hc with ⟨%g, %p, %a, Hg, %hg⟩
  obtain ⟨-, hgk, hC1, hC2⟩ := hg
  let pre (ms : MStore) := preStore cfg lim t ms.store
  let r (ms : MStore) := Exec.step { store := pre ms, thread := t, limits := lim }
  let P' := (gasLoc, gasCellOf g p a) :: (Loc.host, Cell.host (erase h)) :: P
  let Q' (ms : MStore) := (gasLoc, gasCellOf (r ms).store.host.gas (r ms).store.host.gasProfile
    (r ms).store.host.actionProfile) ::
    (Loc.host, Cell.host (erase (r ms).store.host)) :: Q
  have hnot : ∀ (xs : List (Loc × Cell NearState)), (∀ q ∈ xs, isPlain q.1) →
      gasLoc ∉ xs.map (·.1) ∧ Loc.host ∉ xs.map (·.1) := by
    intro xs hx
    constructor <;>
    · intro hm
      obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
      have := hx q hq
      rw [he] at this
      unfold isPlain at this
      simp at this
  have hgh : gasLoc ≠ Loc.host := by decide
  have hnd : ∀ (c1 c2 : Cell NearState) (xs : List (Loc × Cell NearState)), (∀ q ∈ xs, isPlain q.1) →
      (xs.map (·.1)).Nodup → (((gasLoc, c1) :: (Loc.host, c2) :: xs).map (·.1)).Nodup := by
    intro c1 c2 xs hx hn
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or]
    exact ⟨⟨hgh, (hnot xs hx).1⟩, (hnot xs hx).2, hn⟩
  have hfacts : ∀ ms : MStore, (∀ q ∈ Rd, mlookup ms q.1 = some q.2) →
      (∀ q ∈ P', mlookup ms q.1 = some q.2) →
      ms.store.host.gas = g ∧ ms.store.host.gasProfile = p ∧ erase ms.store.host = erase h ∧
      (∀ q ∈ Rd, lookup (pre ms) q.1 = some q.2) ∧ (∀ q ∈ P, lookup (pre ms) q.1 = some q.2) := by
    intro ms hR hPs
    have hgas := hPs _ List.mem_cons_self
    rw [mlookup, if_pos rfl, Option.some.injEq] at hgas
    obtain ⟨h1, h2, -⟩ := gasCellOf_inj hgas
    have hh : mlookup ms Loc.host = some (Cell.host (erase h)) :=
      hPs _ (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [mlookup, if_neg (show Loc.host ≠ gasLoc by decide), if_pos rfl, Option.some.injEq,
      Cell.host.injEq] at hh
    refine ⟨h1, h2, hh, fun q hq => ?_, fun q hq => ?_⟩
    · rw [show pre ms = chargedStore ms.store _ from rfl, lookup_chargedStore_plain _ _ (hRd q hq),
        ← mlookup_plain ms (hRd q hq)]
      exact hR q hq
    · rw [show pre ms = chargedStore ms.store _ from rfl, lookup_chargedStore_plain _ _ (hPp q hq),
        ← mlookup_plain ms (hPp q hq)]
      exact hPs q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  -- The step's facts, on the store the instruction runs on.
  have hrun : ∀ ms : MStore, (∀ q ∈ Rd, mlookup ms q.1 = some q.2) →
      (∀ q ∈ P', mlookup ms q.1 = some q.2) →
      frameTransitionGas cfg { store := pre ms, thread := t, limits := lim } (r ms) = 0 ∧
        ofMachine cfg lim (r ms) = e' ∧ Qh (r ms).store.host ∧
        (r ms).store.host.gas.used ≤ g.used + k + kh ∧
        (r ms).store.host.gas.maxBurnt = g.maxBurnt ∧ (r ms).store.host.gas.prepaid = g.prepaid ∧
        ∀ l, isPlain l → lookup (r ms).store l =
          (Q.lookup l).or (if (P.lookup l).isSome then none else lookup (pre ms) l) := by
    intro ms hR hPs
    obtain ⟨hgas, -, hh, hR', hP''⟩ := hfacts ms hR hPs
    have hpre : (pre ms).host = charged ms.store.host k := by
      show charged ms.store.host _ = _
      rw [hk]
    have hu : (pre ms).host.gas.used = g.used + k := by rw [hpre, charged_gas_used, hgas]
    have hmb : (pre ms).host.gas.maxBurnt = g.maxBurnt := by rw [hpre, ← hgas]; rfl
    have hpp : (pre ms).host.gas.prepaid = g.prepaid := by rw [hpre, ← hgas]; rfl
    obtain ⟨h0, he, hh', hle, hmb', hpp', hpl⟩ := hstep (pre ms) hR' hP''
      (by rw [hpre, erase_charged]; exact hh) (by rw [hu]; omega) (by rw [hmb]; exact hC1)
      (by rw [hpp]; exact hC2)
    exact ⟨h0, he, hh', by rw [hu] at hle; exact hle, by rw [hmb', hmb], by rw [hpp', hpp], hpl⟩
  iapply mwp_lift_dep cfg lim t Rd P' Q' (fun _ => e')
    (hnd _ _ P hPp hP) (fun ms => hnd _ _ Q hQp hQ)
  · intro ms hR hPs
    obtain ⟨hgas, -, hh, -, -⟩ := hfacts ms hR hPs
    obtain ⟨h0, he, hh', hle, hmb, hpp, hpl⟩ := hrun ms hR hPs
    have r1 : (r ms).store.host.gas.used +
        frameTransitionGas cfg { store := pre ms, thread := t, limits := lim } (r ms) ≤ C := by
      rw [h0]; omega
    have r2 : C ≤ (r ms).store.host.gas.maxBurnt := by rw [hmb]; exact hC1
    have r3 : C ≤ (r ms).store.host.gas.prepaid := by rw [hpp]; exact hC2
    rw [mnext_gen cfg lim t ms (C := C) (by rw [hk, hgas]; omega) (by rw [hgas]; exact hC1)
      (by rw [hgas]; exact hC2) r1 r2 r3]
    refine ⟨he, fun l => ?_⟩
    have h0' : frameTransitionGas cfg { store := preStore cfg lim t ms.store, thread := t, limits := lim }
        (Exec.step { store := preStore cfg lim t ms.store, thread := t, limits := lim }) = 0 := h0
    rw [h0', charged_zero]
    have hQnone : ∀ l, ¬ isPlain l → Q.lookup l = none := by
      intro l hl
      cases hq : Q.lookup l with
      | none => rfl
      | some c => exact absurd (hQp (l, c) (mem_of_lookup hq)) hl
    have hPnone : ∀ l, ¬ isPlain l → P.lookup l = none := by
      intro l hl
      cases hq : P.lookup l with
      | none => rfl
      | some c => exact absurd (hPp (l, c) (mem_of_lookup hq)) hl
    by_cases hg : l = gasLoc
    · subst hg
      simp only [mlookup, ↓reduceIte, Q', lookup_cons_pair, Option.some_or]
      rfl
    by_cases hh2 : l = Loc.host
    · subst hh2
      simp only [mlookup, Q', P', lookup_cons_pair, if_neg hg, ↓reduceIte, Option.some_or]
      rfl
    by_cases hp : isPlain l
    · simp only [mlookup, Q', P', lookup_cons_pair, if_neg hg, if_neg hh2]
      rw [hpl l hp, show pre ms = chargedStore ms.store _ from rfl, lookup_chargedStore_plain _ _ hp]
    · simp only [mlookup, Q', P', lookup_cons_pair, if_neg hg, if_neg hh2, hQnone _ hp, hPnone _ hp,
        Option.none_or, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [lookup_other _ hp hh2, lookup_other _ hp hh2]
  · intro ms hR hPs l hl hnone
    obtain ⟨-, -, -, hR', hP''⟩ := hfacts ms hR hPs
    have hgl : l ≠ gasLoc := by
      intro he; subst he; simp [P', lookup_cons_pair] at hnone
    have hhl : l ≠ Loc.host := by
      intro he; subst he; simp [P', lookup_cons_pair] at hnone
    simp only [Q', lookup_cons_pair, if_neg hgl, if_neg hhl] at hl
    simp only [P', lookup_cons_pair, if_neg hgl, if_neg hhl] at hnone
    have hpl : isPlain l := by
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hl
      exact hQp (l, c) (mem_of_lookup hc)
    rw [mlookup_plain ms hpl, ← lookup_chargedStore_plain ms.store
      (nextInstructionGas cfg { store := ms.store, thread := t, limits := lim }) hpl]
    exact hfresh (pre ms) hR' hP'' l hl hnone
  isplitl [HRd]
  · iexact HRd
  isplitl [Hg Hh HP]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hg]
    · iunfold gasPt at Hg
      iexact Hg
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hh]
    · iunfold mhostPt at Hh
      iexact Hh
    · iexact HP
  inext
  iintro %ms %⟨hR, hPs⟩ HQ
  obtain ⟨-, hq, hle, hmb, hpp, -⟩ := (hrun ms hR hPs).2
  icases (BigSepL.bigSepL_cons.1 : _ ⊢ _ ∗ _) $$ HQ with ⟨Hg, HQ⟩
  icases (BigSepL.bigSepL_cons.1 : _ ⊢ _ ∗ _) $$ HQ with ⟨Hh, HQ⟩
  iapply Hwp $$ %((r ms).store.host) %hq [Hh] HQ
  · iunfold mhostPt
    iexact Hh
  iunfold credits
  iexists (r ms).store.host.gas, (r ms).store.host.gasProfile, (r ms).store.host.actionProfile
  isplitl [Hg]
  · iunfold gasPt
    iexact Hg
  · ipureintro
    simp only [Near.GasCounter.used] at hgk hle ⊢
    refine ⟨by omega, by omega, by rw [hmb]; exact hC1, by rw [hpp]; exact hC2⟩

end Host

section Rule

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}

theorem mwpi_call_host_ro_pred (i a n ptr : Nat) (fn : HostFn NearState) (h : NearState) (Q : NearState → Prop) (mx : Option Nat)
    (bs : List UInt8) (vs₀ args rs : List Value) {kh Cg R : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length)
    (hc : ReadContractP fn h Q args rs ptr bs kh Cg) :
    credits Cg (cfg.regularOpCost + kh + R) ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗ mhostPt h ∗
      n ↦[wms][ ptr ] bs ∗
      ▷ (∀ h', ⌜Q h'⌝ -∗ mhostPt h' -∗ n ↦[wms][ ptr ] bs -∗ credits Cg R -∗ Φ.normal (vs₀ ++ rs) f)
      ⊢ mwpi cfg lim d f (vs₀ ++ args) [.call i] Φ := by
  unfold mwpi mKont
  iintro ⟨Hc, #Hf, #Hm, Hh, Hb, HΦ⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  have hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst f.mi), (Loc.func a, Cell.func (.host fn)),
      (Loc.memLimit n, Cell.memLimit mx)], isPlain p.1 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (unfold isPlain; simp)
  iapply mwp_lift_host_pred cfg lim (C.thread f (vs₀ ++ args) C.labels (.call i :: C.rest))
    [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.host fn)), (Loc.memLimit n, .memLimit mx)]
    (byteCells n ptr bs) (byteCells n ptr bs) h Q
    (.running cfg lim (C.thread f (vs₀ ++ rs) C.labels C.rest)) cfg.regularOpCost kh Cg R
    hRd (byteCells_plain n ptr bs) (byteCells_plain n ptr bs) (byteCells_nodup _ _ _)
    (byteCells_nodup _ _ _)
  · intro σ
    exact nextInstructionGas_flat cfg σ lim C f (vs₀ ++ args) C.labels (.call i) C.rest rfl
  · intro σ hR hP hh hu hmb hpp
    have hmi := hmi_of_see hR
    have hfn : σ.funcs[a]? = some (.host fn) := by
      have := hR _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [lookup_func, Option.map_eq_some_iff] at this
      obtain ⟨g, hg, he⟩ := this
      cases he; exact hg
    obtain ⟨mem, hmem, hwf, -⟩ := memLimit_wf
      (hR _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    have hrd : ∀ k, k < bs.length → ptr + k < mem.byteSize ∧ mem.read8 (ptr + k) = bs[k]! := by
      intro k hk
      have := hP _ (mem_byteCells n ptr bs hk)
      simp only [lookup_byte, hmem, Option.bind_some] at this
      split at this
      · rename_i hin; exact ⟨hin.2, by simpa using this⟩
      · cases this
    obtain ⟨host', hcall, hh', hle, hmb', hpp'⟩ := hc σ.host mem hwf hh hrd hu hmb hpp
    have hnlt : n < σ.mems.size := (Array.getElem?_eq_some_iff.mp hmem).1
    have hp := popN_args (C.base ++ vs₀) args
    rw [hlen] at hp
    simp only [List.append_assoc] at hp
    have hstep : Exec.step (Config.mk σ (C.thread f (vs₀ ++ args) C.labels (Instr.call i :: C.rest)) lim) =
        .next (Config.mk { σ with host := host', mems := σ.mems.set! n mem }
          (C.thread f (vs₀ ++ rs) C.labels C.rest) lim) := by
      simp only [Exec.step, Ctx.thread, Ctx.threadA]
      simp [Exec.instr, modules_get! hmi, ha, Exec.enter, hfn, hp, hmi, Store.memOf, hn, hmem,
        hcall, Exec.commitHost, Store.setMemOf]
    rw [hstep, frameTransitionGas_same cfg _ _ (by simp [Config.callDepth, Ctx.thread, Ctx.threadA])]
    refine ⟨rfl, rfl, hh', hle, hmb', hpp', fun l hl => ?_⟩
    have hsame : lookup { σ with host := host', mems := σ.mems.set! n mem } l = lookup σ l := by
      obtain ⟨k, b, j⟩ := l
      have := lookup_setMem { σ with host := host' } n mem (by simpa using hnlt) k b j
      simp only at this
      rw [this, lookup_with_host σ host' _ (by unfold isPlain at hl; simp at hl ⊢; omega)]
      split
      · rename_i hk
        obtain ⟨hk, rfl⟩ := hk
        rw [lookup_mem _ _ _ _ hk, hmem, Option.bind_some]
      · rfl
    show lookup { σ with host := host', mems := σ.mems.set! n mem } l = _
    rw [hsame]
    cases hq : (byteCells (H := NearState) n ptr bs).lookup l with
    | none => simp
    | some c =>
      have := hP _ (mem_of_lookup hq)
      simp only at this
      simp [this]
  · intro σ _ _ l hl hnone
    rw [hnone] at hl
    simp at hl
  isplitl [Hc]
  · iexact Hc
  isplitl [Hh]
  · iexact Hh
  isplitl []
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    isplitr
    · iexact Hi
    iapply (seeList_cons _ _).2
    iunfold funcPt at Hf
    isplitr
    · iexact Hf
    iapply (seeList_cons _ _).2
    iunfold memLimit at Hm
    isplitr
    · iexact Hm
    · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hb]
  · iunfold WasmLogic.memBytes at Hb
    iexact Hb
  inext
  iintro %h' %hq Hh Hb Hc
  icases HK with ⟨HK, -⟩
  ispecialize HK $$ %(vs₀ ++ rs) %f.locals
  simp only [Frame.withLocals_self]
  iapply HK
  iapply HΦ $$ %h' %hq Hh [Hb] Hc
  iunfold WasmLogic.memBytes
  iexact Hb

end Rule

end NearLogic
