import NearLogic.Frag
import WasmLogic.Rules.Call

/-!
# Calling a host function, metered

`mwpi_call_host_ro`: `call i` to a host function that reads some bytes of
the caller's memory and leaves the memory as it was (`value_return`,
`log_utf8`, …). The host function is described by a `ReadContract`: from
any host equal to `h` but for gas, with room for `kh` gas and the bytes in
memory, it returns `rs` and a host equal to `h'` but for gas, having used
at most `kh`.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-- A host function that reads the bytes `bs` at `ptr` and leaves memory alone. -/
def ReadContract (fn : HostFn NearState) (h h' : NearState) (args rs : List Value) (ptr : Nat)
    (bs : List UInt8) (kh C : Nat) : Prop :=
  ∀ (host : NearState) (mem : Memory), mem.wf → erase host = erase h →
    (∀ k, k < bs.length → ptr + k < mem.byteSize ∧ mem.read8 (ptr + k) = bs[k]!) →
    host.gas.used + kh ≤ C → C ≤ host.gas.maxBurnt → C ≤ host.gas.prepaid →
    ∃ host', fn.call host (some mem) args = .return rs host' (some mem) ∧ erase host' = erase h' ∧
      host'.gas.used ≤ host.gas.used + kh ∧ host'.gas.maxBurnt = host.gas.maxBurnt ∧
      host'.gas.prepaid = host.gas.prepaid

theorem byteCells_plain (n i : Nat) (bs : List UInt8) : ∀ p ∈ byteCells (H := NearState) n i bs, isPlain p.1 := by
  intro p hp
  have := lookup_byteCells (H := NearState) n i bs p.1
  rw [lookup_of_mem (byteCells_nodup _ _ _) hp] at this
  split at this
  · rename_i h; unfold isPlain; rw [h.1]; omega
  · cases this

section Rule

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}

theorem memLimit_wf {σ : Store NearState} {n : Nat} {mx : Option Nat}
    (h : lookup σ (Loc.memLimit n) = some (Cell.memLimit mx)) :
    ∃ mem, σ.mems[n]? = some mem ∧ mem.wf ∧ mem.max = mx := by
  simp only [lookup_memLimit, Option.bind_eq_some_iff] at h
  obtain ⟨mem, hmem, h⟩ := h
  split at h
  · rename_i hw; cases h; exact ⟨mem, hmem, hw, rfl⟩
  · cases h

theorem mwpi_call_host_ro (i a n ptr : Nat) (fn : HostFn NearState) (h h' : NearState) (mx : Option Nat)
    (bs : List UInt8) (vs₀ args rs : List Value) {kh Cg R : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length)
    (hc : ReadContract fn h h' args rs ptr bs kh Cg) :
    credits Cg (cfg.regularOpCost + kh + R) ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗ mhostPt h ∗
      n ↦[wms][ ptr ] bs ∗
      ▷ (mhostPt h' -∗ n ↦[wms][ ptr ] bs -∗ credits Cg R -∗ Φ.normal (vs₀ ++ rs) f)
      ⊢ mwpi cfg lim d f (vs₀ ++ args) [.call i] Φ := by
  unfold mwpi mKont
  iintro ⟨Hc, #Hf, #Hm, Hh, Hb, HΦ⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  have hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst f.mi), (Loc.func a, Cell.func (.host fn)),
      (Loc.memLimit n, Cell.memLimit mx)], isPlain p.1 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> (unfold isPlain; simp)
  iapply mwp_lift_host cfg lim (C.thread f (vs₀ ++ args) C.labels (.call i :: C.rest))
    [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.host fn)), (Loc.memLimit n, .memLimit mx)]
    (byteCells n ptr bs) (byteCells n ptr bs) h h'
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
  iintro Hh Hb Hc
  icases HK with ⟨HK, -⟩
  ispecialize HK $$ %(vs₀ ++ rs) %f.locals
  simp only [Frame.withLocals_self]
  iapply HK
  iapply HΦ $$ Hh [Hb] Hc
  iunfold WasmLogic.memBytes
  iexact Hb

end Rule

end NearLogic
