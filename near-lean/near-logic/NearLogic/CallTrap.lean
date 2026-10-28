import NearLogic.CallPred

/-!
# Calling a host function that traps

`TrapContractP` is `ReadContractP` for a host function that ends the run: it
reads the bytes `bs` at `ptr`, leaves memory alone, and traps with the reason
`r` and a host satisfying `Q` (`panic_utf8`, `abort`). `mwpi_call_host_trap`
is the `call i` rule: the fragment ends with the postcondition's `trap`, given
the resulting host `h'` and `Q h'`.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-- A host function that reads the bytes `bs` at `ptr`, leaves memory alone,
and traps with the reason `r` and a host satisfying `Q`. -/
def TrapContractP (fn : HostFn NearState) (h : NearState) (Q : NearState → Prop) (args : List Value)
    (r : Trap) (ptr : Nat) (bs : List UInt8) (kh C : Nat) : Prop :=
  ∀ (host : NearState) (mem : Memory), mem.wf → erase host = erase h →
    (∀ k, k < bs.length → ptr + k < mem.byteSize ∧ mem.read8 (ptr + k) = bs[k]!) →
    host.gas.used + kh ≤ C → C ≤ host.gas.maxBurnt → C ≤ host.gas.prepaid →
    ∃ host', fn.call host (some mem) args = .trap r host' (some mem) ∧ Q host' ∧
      host'.gas.used ≤ host.gas.used + kh ∧ host'.gas.maxBurnt = host.gas.maxBurnt ∧
      host'.gas.prepaid = host.gas.prepaid

theorem TrapContractP.mono {fn : HostFn NearState} {h : NearState} {Q Q' : NearState → Prop}
    {args : List Value} {r : Trap} {ptr : Nat} {bs : List UInt8} {kh C : Nat}
    (hc : TrapContractP fn h Q args r ptr bs kh C) (hQ : ∀ x, Q x → Q' x) :
    TrapContractP fn h Q' args r ptr bs kh C := by
  intro host mem hwf he hrd hu hmb hpp
  obtain ⟨host', h1, h2, h3⟩ := hc host mem hwf he hrd hu hmb hpp
  exact ⟨host', h1, hQ _ h2, h3⟩

section Rule

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}

/-- **A host call that traps.** The fragment `call i` ends with `Φ.trap`, from
the resulting host `h'` with `Q h'`, the bytes and the credits left. -/
theorem mwpi_call_host_trap (i a n ptr : Nat) (fn : HostFn NearState) (h : NearState) (Q : NearState → Prop)
    (mx : Option Nat) (bs : List UInt8) (vs₀ args : List Value) (r : Trap) {kh Cg R : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length)
    (hc : TrapContractP fn h Q args r ptr bs kh Cg) :
    credits Cg (cfg.regularOpCost + kh + R) ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗ mhostPt h ∗
      n ↦[wms][ ptr ] bs ∗
      ▷ (∀ h', ⌜Q h'⌝ -∗ mhostPt h' -∗ n ↦[wms][ ptr ] bs -∗ credits Cg R -∗ Φ.trap)
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
    (byteCells n ptr bs) (byteCells n ptr bs) h Q (.finished (.trap r)) cfg.regularOpCost kh Cg R
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
        .trap r { σ with host := host', mems := σ.mems.set! n mem } := by
      simp only [Exec.step, Ctx.thread, Ctx.threadA]
      simp [Exec.instr, modules_get! hmi, ha, Exec.enter, hfn, hp, hmi, Store.memOf, hn, hmem,
        hcall, Exec.commitHost, Store.setMemOf]
    rw [hstep]
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
  iunfold WasmLogic.memBytes at HΦ
  inext
  iintro %h' %hq Hh Hb Hc
  icases HK with ⟨-, -, -, HK⟩
  iapply mwp_finished
  ispecialize HΦ $$ %h' %hq Hh Hb Hc
  ispecialize HK $$ HΦ
  ispecialize HK $$ %r
  iexact HK

end Rule

end NearLogic
