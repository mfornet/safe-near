import NearLogic.Rules.Pure
import NearLogic.Call
import NearLogic.Hosts.ValueReturn
import NearLogic.Method
import NearLogic.Adequacy

/-!
# Walking skeleton: a method that returns a constant

The smallest method that goes through every layer (milestone M2): `get`
returns the four bytes `"ok"` (quotes included) from the data segment at
address 0, through `value_return`:

```wat
(module
  (import "env" "value_return" (func $value_return (param i64 i64)))
  (memory 1)
  (data (i32.const 0) "\"ok\"")
  (func (export "get") (call $value_return (i64.const 4) (i64.const 0))))
```

This file proves its body, from the bytes in memory and credits for its
three instructions and the host call, to falling through with the return
data selected.
-/

namespace NearLogic.Skeleton

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

/-- The returned bytes: `"ok"`, quotes included. -/
def okBytes : List UInt8 := [34, 111, 107, 34]

/-- The body of `get`. -/
def body : List Instr := [.i64_const 4, .i64_const 0, .call 0]

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The body of `get`: from the host `h`, the four bytes at address 0 and
credits for three instructions and `value_return`, it falls through with
nothing on the stack and `"ok"` as the return data. -/
theorem body_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (f : Frame) (extra : Nat)
    (h : NearState) (a n : Nat) (mx : Option Nat) {Cg R : Nat} {Φ : Post NearState GF}
    (ha : f.mi.funcAddrs[0]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlim : withinLimit h.config.maxReturnLen 4 = true) :
    credits Cg (3 * cfg.regularOpCost + valueReturnUse h 4 + R) ∗
      a ↪[wf] FuncInst.host (metered extra "value_return" valueReturnFn).toHostFn ∗
      n ↪[wmlimit] mx ∗ mhostPt h ∗ n ↦[wms][ 0 ] okBytes ∗
      ▷ ▷ ▷ (mhostPt (h.selectReturnValue okBytes) -∗ n ↦[wms][ 0 ] okBytes -∗ credits Cg R -∗
        Φ.normal [] f)
      ⊢ mwpi cfg lim d f [] body Φ := by
  iintro ⟨Hc, #Hf, #Hm, Hh, Hb, HΦ⟩
  unfold body
  iapply mwpi_cons
  iapply mwpi_i64_const (R := cfg.regularOpCost + (cfg.regularOpCost + valueReturnUse h 4 + R))
  isplitl [Hc]
  · rw [show 3 * cfg.regularOpCost + valueReturnUse h 4 + R =
      cfg.regularOpCost + (cfg.regularOpCost + (cfg.regularOpCost + valueReturnUse h 4 + R)) by omega]
    iexact Hc
  inext
  iintro Hc
  simp only [Post.mseq_normal, List.nil_append]
  iapply mwpi_cons
  iapply mwpi_i64_const (R := cfg.regularOpCost + valueReturnUse h 4 + R)
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  simp only [Post.mseq_normal]
  have hc : ReadContract (metered extra "value_return" valueReturnFn).toHostFn h (h.selectReturnValue okBytes)
      [.i64 4, .i64 0] [] 0 okBytes (valueReturnUse h 4) Cg :=
    valueReturn_readContract (C := Cg) extra h 4 0 okBytes (by decide) rfl hlim (by decide)
  rw [show ([Value.i64 4] ++ [Value.i64 0]) = ([] : List Value) ++ [.i64 4, .i64 0] from rfl]
  iapply mwpi_call_host_ro 0 a n 0 _ h _ mx okBytes [] [.i64 4, .i64 0] [] ha hn rfl hc
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iexact Hf
  isplitr
  · iexact Hm
  isplitl [Hh]
  · iexact Hh
  isplitl [Hb]
  · iexact Hb
  inext
  iintro Hh Hb Hc
  simp only [List.nil_append]
  iapply HΦ $$ Hh Hb Hc

/-! ## The whole thread -/

/-- What `get` leaves: no values, `"ok"` as the return data, and at most
`Cg` gas used. -/
def GetEnds (Cg : Nat) (v : Ending) (σ' : MStore) : Prop :=
  v = .values [] ∧ σ'.store.host.returnData = some okBytes ∧ σ'.store.host.gas.used ≤ Cg

/-- The cells `get` hands back: the host, and the gas counter within `Cg`. -/
def getCells (Cg : Nat) (cs : List (Loc × Cell NearState)) : Prop :=
  ∃ (h : NearState) (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)),
    cs = [(Loc.host, .host (erase h)), (gasLoc, gasCellOf g p a)] ∧
      h.returnData = some okBytes ∧ g.used ≤ Cg

theorem getCells_ends {Cg : Nat} {σ' : MStore} {cs : List (Loc × Cell NearState)} (hc : getCells Cg cs)
    (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    σ'.store.host.returnData = some okBytes ∧ σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h, g, p, a, rfl, hr, hg⟩ := hc
  have h1 := hl _ List.mem_cons_self
  have h2 := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at h1 h2
  obtain ⟨hg', -, -⟩ := gasCellOf_inj h2
  have hrd : σ'.store.host.returnData = h.returnData :=
    erase_field h1 NearState.returnData fun _ => rfl
  exact ⟨hrd.trans hr, hg' ▸ hg⟩

/-- `get`, run as the only frame from a store that holds its instance, the
`value_return` import, a memory with `"ok"` at address 0, and room for its
gas within `Cg`: it ends with no values, `"ok"` as the return data and at
most `Cg` gas used. -/
theorem get_adequate (cfg : WasmConfig) (lim : ExecLimits) (extra : Nat) (σ : Store NearState)
    (locals : Array Value) (inst a n : Nat) (mi : ModuleInst) (mem : Memory) (Cg : Nat)
    (hmod : σ.modules[inst]? = some mi) (ha : mi.funcAddrs[0]? = some a) (hn : mi.memAddrs[0]? = some n)
    (hfn : σ.funcs[a]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hmem : σ.mems[n]? = some mem) (hwf : mem.wf = true)
    (hbytes : ∀ k, k < 4 → k < mem.byteSize ∧ mem.read8 k = okBytes[k]!)
    (hlim : withinLimit σ.host.config.maxReturnLen 4 = true)
    (hgas : σ.host.gas.used + (3 * cfg.regularOpCost + valueReturnUse σ.host 4) ≤ Cg)
    (hC1 : Cg ≤ σ.host.gas.maxBurnt) (hC2 : Cg ≤ σ.host.gas.prepaid) :
    adequate .MaybeStuck (MCode.running cfg lim (entryThread ⟨locals, inst, mi⟩ 0 body)) ⟨σ⟩
      (GetEnds Cg) := by
  have had := mwp_adequacy_cells (GF' := WasmLogic.GF NearState)
    (MCode.running cfg lim (entryThread ⟨locals, inst, mi⟩ 0 body)) ⟨σ⟩ (fun v => v = .values [])
    (fun _ cs => getCells Cg cs) ?_
  · refine ⟨fun t2 σ2 v2 hr => ?_, fun t2 σ2 e2 hs hr hm => had.adequate_not_stuck t2 σ2 e2 hs hr hm⟩
    obtain ⟨hv, cs, hc, hl⟩ := had.adequate_result t2 σ2 v2 hr
    exact ⟨hv, getCells_ends hc hl⟩
  intro _
  let fn := (metered extra "value_return" valueReturnFn).toHostFn
  let f : Frame := ⟨locals, inst, mi⟩
  let xs : List (Loc × Cell NearState) :=
    [(Loc.inst inst, .inst mi), (Loc.func a, .func (.host fn)), (Loc.memLimit n, .memLimit mem.max),
      (Loc.host, .host (erase σ.host)),
      (gasLoc, gasCellOf σ.host.gas σ.host.gasProfile σ.host.actionProfile)] ++ byteCells n 0 okBytes
  have hbc : ∀ p ∈ byteCells (H := NearState) n 0 okBytes, p.1.1 = 0 := by
    intro p hp
    have := lookup_byteCells (H := NearState) n 0 okBytes p.1
    rw [lookup_of_mem (byteCells_nodup _ _ _) hp] at this
    split at this
    · rename_i h; exact h.1
    · cases this
  have hnd : (xs.map (·.1)).Nodup := by
    simp only [xs, List.map_append, List.nodup_append, List.map_cons, List.map_nil]
    refine ⟨by simp, byteCells_nodup _ _ _, ?_⟩
    intro l hl l' hl'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl'
    have := hbc q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> (intro he; rw [← he] at this; simp at this)
  have hget : ∀ p ∈ xs, Iris.Std.PartialMap.get? (mheapOf ⟨σ⟩) p.1 = some p.2 := by
    intro p hp
    rw [get?_mheapOf]
    simp only [xs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl) | hp
    · rw [mlookup_plain _ (by unfold isPlain; simp)]; simp [hmod]
    · rw [mlookup_plain _ (by unfold isPlain; simp)]; simp [hfn, fn]
    · rw [mlookup_plain _ (by unfold isPlain; simp)]; simp [hmem, hwf]
    · simp [mlookup]
    · simp [mlookup]
    · have hz := hbc p hp
      rw [mlookup_plain _ (by unfold isPlain; rw [hz]; omega)]
      have := lookup_byteCells (H := NearState) n 0 okBytes p.1
      rw [lookup_of_mem (byteCells_nodup _ _ _) hp] at this
      split at this
      · rename_i hk
        obtain ⟨⟨k, b, j⟩, c⟩ := p
        simp only at hk this ⊢
        obtain ⟨rfl, rfl, -, hj⟩ := hk
        simp only [Option.some.injEq] at this
        subst this
        have := hbytes j (by simpa [okBytes] using hj)
        simp [hmem, hwf, this.1, this.2]
      · cases this
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜v = .values []⌝ ∗ mcellsSat (fun cs => getCells Cg cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  iintro Hcells
  ihave Hxs := ownCells_take (mheapOf ⟨σ⟩) xs hnd hget $$ Hcells
  simp only [xs, List.cons_append, List.nil_append]
  icases (BigSepL.bigSepL_cons.1 : _ ⊢ _ ∗ _) $$ Hxs with ⟨Hi, Hxs⟩
  icases (BigSepL.bigSepL_cons.1 : _ ⊢ _ ∗ _) $$ Hxs with ⟨Hf, Hxs⟩
  icases (BigSepL.bigSepL_cons.1 : _ ⊢ _ ∗ _) $$ Hxs with ⟨Hm, Hxs⟩
  icases (BigSepL.bigSepL_cons.1 : _ ⊢ _ ∗ _) $$ Hxs with ⟨Hh, Hxs⟩
  icases (BigSepL.bigSepL_cons.1 : _ ⊢ _ ∗ _) $$ Hxs with ⟨Hg, Hb⟩
  iapply fupd_wp
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hf with #Hf
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imodintro
  iapply mwp_entry cfg lim f 0 body Cg Ψ
  isplitr
  · iunfold instPt
    iexact Hi
  iapply body_spec cfg lim 0 f extra σ.host a n mem.max (Cg := Cg) (R := 0) (Φ := entryPost Cg 0 Ψ) ha hn hlim
  isplitl [Hg]
  · iunfold credits
    iexists σ.host.gas, σ.host.gasProfile, σ.host.actionProfile
    isplitl [Hg]
    · iunfold gasPt
      iexact Hg
    · ipureintro
      simp only [Near.GasCounter.used] at hgas ⊢
      omega
  isplitr
  · iunfold funcPt
    iexact Hf
  isplitr
  · iunfold memLimit
    iexact Hm
  isplitl [Hh]
  · iunfold mhostPt
    iexact Hh
  isplitl [Hb]
  · iunfold WasmLogic.memBytes
    iexact Hb
  inext
  inext
  inext
  iintro Hh _ Hc
  simp only [entryPost]
  isplitr
  · ipureintro; rfl
  iexists 0
  isplitl [Hc]
  · iexact Hc
  iintro Hc
  isplitr
  · ipureintro; rfl
  iunfold credits at Hc
  icases Hc with ⟨%g, %p, %a', Hg, %hg⟩
  iexists [(Loc.host, Cell.host (erase (σ.host.selectReturnValue okBytes))), (gasLoc, gasCellOf g p a')]
  isplitr
  · ipureintro
    refine ⟨⟨_, g, p, a', rfl, rfl, by omega⟩, by simp only [List.map_cons, List.map_nil]; decide⟩
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hh]
  · iunfold mhostPt at Hh
    iexact Hh
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hg]
  · iunfold gasPt at Hg
    iexact Hg
  iapply BigSepL.bigSepL_nil.2
  iempintro

end NearLogic.Skeleton
