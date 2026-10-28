import NearLogic.CallPred

/-!
# Calling a host function that reads two byte ranges

`ReadContractP2` is `ReadContractP` for a host function that reads two disjoint byte ranges of
the caller's memory (`storage_write`: the key and the value), and `mwpi_call_host_ro_pred2` the
corresponding `call i` rule.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-- A host function that reads the bytes `b1` at `p1` and `b2` at `p2`, leaves memory alone, and
ends with a host satisfying `Q`. -/
def ReadContractP2 (fn : HostFn NearState) (h : NearState) (Q : NearState → Prop) (args rs : List Value)
    (p1 : Nat) (b1 : List UInt8) (p2 : Nat) (b2 : List UInt8) (kh C : Nat) : Prop :=
  ∀ (host : NearState) (mem : Memory), mem.wf → erase host = erase h →
    (∀ k, k < b1.length → p1 + k < mem.byteSize ∧ mem.read8 (p1 + k) = b1[k]!) →
    (∀ k, k < b2.length → p2 + k < mem.byteSize ∧ mem.read8 (p2 + k) = b2[k]!) →
    host.gas.used + kh ≤ C → C ≤ host.gas.maxBurnt → C ≤ host.gas.prepaid →
    ∃ host', fn.call host (some mem) args = .return rs host' (some mem) ∧ Q host' ∧
      host'.gas.used ≤ host.gas.used + kh ∧ host'.gas.maxBurnt = host.gas.maxBurnt ∧
      host'.gas.prepaid = host.gas.prepaid

theorem ReadContractP2.mono {fn : HostFn NearState} {h : NearState} {Q Q' : NearState → Prop}
    {args rs : List Value} {p1 p2 : Nat} {b1 b2 : List UInt8} {kh C : Nat}
    (hc : ReadContractP2 fn h Q args rs p1 b1 p2 b2 kh C) (hQ : ∀ x, Q x → Q' x) :
    ReadContractP2 fn h Q' args rs p1 b1 p2 b2 kh C := by
  intro host mem hwf he hrd1 hrd2 hu hmb hpp
  obtain ⟨host', h1, h2, h3⟩ := hc host mem hwf he hrd1 hrd2 hu hmb hpp
  exact ⟨host', h1, hQ _ h2, h3⟩

theorem mem_byteCells_loc {n i : Nat} {bs : List UInt8} {l : Loc}
    (h : l ∈ (byteCells (H := NearState) n i bs).map (·.1)) : l.2.1 = n ∧ i ≤ l.2.2 ∧ l.2.2 < i + bs.length := by
  induction bs generalizing i with
  | nil => simp [byteCells] at h
  | cons b bs ih =>
    simp only [byteCells, List.map_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨a, b, c⟩ := ih h
      simp only [List.length_cons]
      omega

theorem byteCells_nodup2 (n p1 p2 : Nat) (b1 b2 : List UInt8)
    (hd : p1 + b1.length ≤ p2 ∨ p2 + b2.length ≤ p1) :
    ((byteCells (H := NearState) n p1 b1 ++ byteCells (H := NearState) n p2 b2).map (·.1)).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨byteCells_nodup n p1 b1, byteCells_nodup n p2 b2, ?_⟩
  intro a ha b hb hab
  subst hab
  have h1 := mem_byteCells_loc ha
  have h2 := mem_byteCells_loc hb
  omega

section Rule

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}

theorem mwpi_call_host_ro_pred2 (i a n p1 p2 : Nat) (fn : HostFn NearState) (h : NearState)
    (Q : NearState → Prop) (mx : Option Nat) (b1 b2 : List UInt8) (vs₀ args rs : List Value) {kh Cg R : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length)
    (hd : p1 + b1.length ≤ p2 ∨ p2 + b2.length ≤ p1)
    (hc : ReadContractP2 fn h Q args rs p1 b1 p2 b2 kh Cg) :
    credits Cg (cfg.regularOpCost + kh + R) ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗ mhostPt h ∗
      n ↦[wms][ p1 ] b1 ∗ n ↦[wms][ p2 ] b2 ∗
      ▷ (∀ h', ⌜Q h'⌝ -∗ mhostPt h' -∗ n ↦[wms][ p1 ] b1 -∗ n ↦[wms][ p2 ] b2 -∗ credits Cg R -∗
        Φ.normal (vs₀ ++ rs) f)
      ⊢ mwpi cfg lim d f (vs₀ ++ args) [.call i] Φ := by
  unfold mwpi mKont
  iintro ⟨Hc, #Hf, #Hm, Hh, Hb1, Hb2, HΦ⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  have hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst f.mi), (Loc.func a, Cell.func (.host fn)),
      (Loc.memLimit n, Cell.memLimit mx)], isPlain p.1 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (unfold isPlain; simp)
  have hPp : ∀ p ∈ byteCells (H := NearState) n p1 b1 ++ byteCells n p2 b2, isPlain p.1 := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact byteCells_plain n p1 b1 p hp
    · exact byteCells_plain n p2 b2 p hp
  iapply mwp_lift_host_pred cfg lim (C.thread f (vs₀ ++ args) C.labels (.call i :: C.rest))
    [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.host fn)), (Loc.memLimit n, .memLimit mx)]
    (byteCells n p1 b1 ++ byteCells n p2 b2) (byteCells n p1 b1 ++ byteCells n p2 b2) h Q
    (.running cfg lim (C.thread f (vs₀ ++ rs) C.labels C.rest)) cfg.regularOpCost kh Cg R
    hRd hPp hPp (byteCells_nodup2 n p1 p2 b1 b2 hd) (byteCells_nodup2 n p1 p2 b1 b2 hd)
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
    have hrd : ∀ (p : Nat) (bs : List UInt8), (∀ q ∈ byteCells (H := NearState) n p bs,
        lookup σ q.1 = some q.2) →
        ∀ k, k < bs.length → p + k < mem.byteSize ∧ mem.read8 (p + k) = bs[k]! := by
      intro p bs hPb k hk
      have := hPb _ (mem_byteCells n p bs hk)
      simp only [lookup_byte, hmem, Option.bind_some] at this
      split at this
      · rename_i hin; exact ⟨hin.2, by simpa using this⟩
      · cases this
    have hrd1 := hrd p1 b1 fun q hq => hP q (List.mem_append_left _ hq)
    have hrd2 := hrd p2 b2 fun q hq => hP q (List.mem_append_right _ hq)
    obtain ⟨host', hcall, hh', hle, hmb', hpp'⟩ := hc σ.host mem hwf hh hrd1 hrd2 hu hmb hpp
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
    cases hq : (byteCells (H := NearState) n p1 b1 ++ byteCells n p2 b2).lookup l with
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
  isplitl [Hb1 Hb2]
  · iunfold WasmLogic.memBytes at Hb1 Hb2
    iapply BigSepL.bigSepL_append.2
    iframe Hb1 Hb2
  inext
  iintro %h' %hq Hh Hb Hc
  icases (BigSepL.bigSepL_append.1 : _ ⊢ _ ∗ _) $$ Hb with ⟨Hb1, Hb2⟩
  icases HK with ⟨HK, -⟩
  ispecialize HK $$ %(vs₀ ++ rs) %f.locals
  simp only [Frame.withLocals_self]
  iapply HK
  iapply HΦ $$ %h' %hq Hh [Hb1] [Hb2] Hc
  · iunfold WasmLogic.memBytes
    iexact Hb1
  · iunfold WasmLogic.memBytes
    iexact Hb2

end Rule

end NearLogic
