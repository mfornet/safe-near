import NearLogic.Call

/-!
# Calling a host function that writes memory, metered

`mwpi_call_host_rw`: `call i` to a host function that replaces the bytes
`old` at `ptr` of the caller's memory by `new` (same length) and touches
nothing else of it (`read_register`, …). The host function is described by
an `RWContract`: from any host equal to `h` but for gas, with room for `kh`
gas and `old` in memory, it returns `rs`, a host equal to `h'` but for gas
having used at most `kh`, and the memory with `new` written at `ptr`
(`WritesAt`).
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-- `mem'` is `mem` with `new` written at `addr`: same size and limit, and
every other byte as it was. -/
structure WritesAt (mem mem' : Memory) (addr : Nat) (new : List UInt8) : Prop where
  wf : mem'.wf
  byteSize : mem'.byteSize = mem.byteSize
  max : mem'.max = mem.max
  read8 : ∀ j, mem'.read8 j = if addr ≤ j ∧ j < addr + new.length then new[j - addr]! else mem.read8 j

/-- A host function that replaces the bytes `old` at `ptr` by `new`. It reads
nothing else of the memory. -/
def RWContract (fn : HostFn NearState) (h h' : NearState) (args rs : List Value) (ptr : Nat)
    (old new : List UInt8) (kh C : Nat) : Prop :=
  ∀ (host : NearState) (mem : Memory), mem.wf → erase host = erase h →
    (∀ k, k < old.length → ptr + k < mem.byteSize ∧ mem.read8 (ptr + k) = old[k]!) →
    host.gas.used + kh ≤ C → C ≤ host.gas.maxBurnt → C ≤ host.gas.prepaid →
    ∃ host' mem', fn.call host (some mem) args = .return rs host' (some mem') ∧
      WritesAt mem mem' ptr new ∧ erase host' = erase h' ∧
      host'.gas.used ≤ host.gas.used + kh ∧ host'.gas.maxBurnt = host.gas.maxBurnt ∧
      host'.gas.prepaid = host.gas.prepaid

/-! ## `writeList` within bounds -/

theorem writeList_fold_spec (data : List UInt8) : ∀ (m : Memory) (addr : Nat), m.wf →
    addr + data.length ≤ m.byteSize →
    WritesAt m (data.foldl (fun (m, a) b => (if a < m.byteSize then m.write8 a b else m, a + 1))
      (m, addr)).1 addr data ∧
    (data.foldl (fun (m, a) b => (if a < m.byteSize then m.write8 a b else m, a + 1)) (m, addr)).2 =
      addr + data.length := by
  induction data with
  | nil =>
    intro m addr hwf _
    refine ⟨⟨hwf, rfl, rfl, fun j => ?_⟩, by simp⟩
    simp only [List.length_nil, Nat.add_zero]
    rw [if_neg (by omega)]; rfl
  | cons b bs ih =>
    intro m addr hwf hb
    simp only [List.length_cons] at hb
    simp only [List.foldl_cons]
    rw [if_pos (by omega)]
    obtain ⟨hw, ha⟩ := ih (m.write8 addr b) (addr + 1) (Memory.write8_wf hwf _ _)
      (by rw [Memory.write8_byteSize]; omega)
    refine ⟨⟨hw.wf, by rw [hw.byteSize, Memory.write8_byteSize], by rw [hw.max, Memory.write8_max],
      fun j => ?_⟩, by rw [ha]; simp; omega⟩
    rw [hw.read8, Memory.read8_write8 hwf (by omega)]
    simp only [List.length_cons]
    by_cases h1 : addr + 1 ≤ j ∧ j < addr + 1 + bs.length
    · rw [if_pos h1, if_pos (by omega)]
      have : j - addr = (j - (addr + 1)) + 1 := by omega
      rw [this]; simp
    · rw [if_neg h1]
      by_cases hj : j = addr
      · subst hj; simp
      · rw [if_neg hj, if_neg (by omega)]

/-- Writing a list within bounds writes exactly its bytes. -/
theorem writeList_spec {m : Memory} (hwf : m.wf) {addr : Nat} {data : List UInt8}
    (hb : addr + data.length ≤ m.byteSize) : WritesAt m (m.writeList addr data) addr data := by
  unfold Memory.writeList
  exact (writeList_fold_spec data m addr hwf hb).1

/-! ## The cells a write replaces -/

/-- Writing `new` over `old` (same length) replaces exactly their cells. -/
theorem replaces_writesAt {H : Type} {σ : Store H} {n addr : Nat} {mem mem' : Memory}
    (hmem : σ.mems[n]? = some mem) (hwf : mem.wf) {old new : List UInt8}
    (hb : ∀ k, k < old.length → addr + k < mem.byteSize) (hl : new.length = old.length)
    (hw : WritesAt mem mem' addr new) :
    Replaces σ { σ with mems := σ.mems.set! n mem' } (byteCells n addr old) (byteCells n addr new) := by
  have hn : n < σ.mems.size := (Array.getElem?_eq_some_iff.mp hmem).1
  intro ⟨k, a, i⟩
  rw [lookup_setMem _ _ _ hn, lookup_byteCells, lookup_byteCells, hl]
  by_cases hk : (k = 0 ∨ k = 1) ∧ a = n
  · rw [ite_eq_left hk]
    obtain ⟨hk, rfl⟩ := hk
    rw [lookup_mem _ _ _ _ hk, hmem, Option.bind_some]
    rcases hk with rfl | rfl
    · by_cases hi : addr ≤ i ∧ i < addr + old.length
      · have hlt : i < mem.byteSize := by
          have := hb (i - addr) (by omega); rwa [Nat.add_sub_cancel' hi.1] at this
        simp only [hi, and_self, ite_true, memCell, hw.wf, hw.byteSize, hw.read8, hl, hlt,
          Option.some_or]
      · have hi' : ¬(addr ≤ i ∧ i < addr + old.length) := hi
        simp [memCell, hwf, hw.wf, hw.byteSize, hw.read8, hl, hi']
    · rcases i with _ | _ | i <;> simp [memCell, hwf, hw.wf, hw.byteSize, hw.max]
  · rw [ite_eq_right hk]
    have : ¬(k = 0 ∧ a = n ∧ addr ≤ i ∧ i < addr + old.length) := fun h => hk ⟨.inl h.1, h.2.1⟩
    simp [this]

section Rule

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}

theorem mwpi_call_host_rw (i a n ptr : Nat) (fn : HostFn NearState) (h h' : NearState) (mx : Option Nat)
    (old new : List UInt8) (vs₀ args rs : List Value) {kh Cg R : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length) (hl : new.length = old.length)
    (hc : RWContract fn h h' args rs ptr old new kh Cg) :
    credits Cg (cfg.regularOpCost + kh + R) ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗ mhostPt h ∗
      n ↦[wms][ ptr ] old ∗
      ▷ (mhostPt h' -∗ n ↦[wms][ ptr ] new -∗ credits Cg R -∗ Φ.normal (vs₀ ++ rs) f)
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
    (byteCells n ptr old) (byteCells n ptr new) h h'
    (.running cfg lim (C.thread f (vs₀ ++ rs) C.labels C.rest)) cfg.regularOpCost kh Cg R
    hRd (byteCells_plain n ptr old) (byteCells_plain n ptr new) (byteCells_nodup _ _ _)
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
    have hrd : ∀ k, k < old.length → ptr + k < mem.byteSize ∧ mem.read8 (ptr + k) = old[k]! := by
      intro k hk
      have := hP _ (mem_byteCells n ptr old hk)
      simp only [lookup_byte, hmem, Option.bind_some] at this
      split at this
      · rename_i hin; exact ⟨hin.2, by simpa using this⟩
      · cases this
    obtain ⟨host', mem', hcall, hw, hh', hle, hmb', hpp'⟩ := hc σ.host mem hwf hh hrd hu hmb hpp
    have hp := popN_args (C.base ++ vs₀) args
    rw [hlen] at hp
    simp only [List.append_assoc] at hp
    have hstep : Exec.step (Config.mk σ (C.thread f (vs₀ ++ args) C.labels (Instr.call i :: C.rest)) lim) =
        .next (Config.mk { σ with host := host', mems := σ.mems.set! n mem' }
          (C.thread f (vs₀ ++ rs) C.labels C.rest) lim) := by
      simp only [Exec.step, Ctx.thread, Ctx.threadA]
      simp [Exec.instr, modules_get! hmi, ha, Exec.enter, hfn, hp, hmi, Store.memOf, hn, hmem,
        hcall, Exec.commitHost, Store.setMemOf]
    rw [hstep, frameTransitionGas_same cfg _ _ (by simp [Config.callDepth, Ctx.thread, Ctx.threadA])]
    refine ⟨rfl, rfl, hh', hle, hmb', hpp', fun l hpl => ?_⟩
    show lookup { σ with host := host', mems := σ.mems.set! n mem' } l = _
    have hrep := replaces_writesAt (σ := { σ with host := host' }) (n := n) hmem hwf
      (fun k hk => (hrd k hk).1) hl hw l
    simp only at hrep ⊢
    rw [hrep, lookup_with_host σ host' _ (by unfold isPlain at hpl; omega)]
  · intro σ _ _ l hq hnone
    rw [lookup_byteCells] at hq hnone
    rw [hl] at hq
    split at hq
    · rw [if_pos (by assumption)] at hnone; cases hnone
    · cases hq
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
