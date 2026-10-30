import NearLogic.Call
import WasmLogic.Rules.Memory

/-!
# Memory and global rules, metered

WasmLogic's memory and global rules (`WasmLogic/Rules/Memory.lean`), each for
one `regular_op_cost` of credits.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.ProgramLogic

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg R : Nat}

theorem mwpi_load (t : NumType) (packed : Option Packed) (arg : MemArg) (a : UInt32) (n : Nat)
    (bs : List UInt8) (hn : f.mi.memAddrs[0]? = some n) (hlen : bs.length = loadWidth t packed)
    (hne : bs ≠ []) :
    credits Cg (cfg.regularOpCost + R) ∗ n ↦[wms][ a.toNat + arg.offset ] bs ∗
      ▷ (n ↦[wms][ a.toNat + arg.offset ] bs -∗ credits Cg R -∗
          Φ.normal (vs ++ [loadValue t packed (Memory.decodeLE bs)]) f)
      ⊢ mwpi cfg lim d f (vs ++ [.i32 a]) [.load t packed arg] Φ := by
  have key := mwpi_instr (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 a])
    (Cg := Cg) (R := R)
    (.load t packed arg) rfl (vs ++ [loadValue t packed (Memory.decodeLE bs)]) f.locals []
    (byteCells n (a.toNat + arg.offset) bs) (byteCells n (a.toNat + arg.offset) bs)
    (by simp) (byteCells_plain _ _ _) (byteCells_plain _ _ _)
    (byteCells_nodup _ _ _) (byteCells_nodup _ _ _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, _, hb, hrd⟩ := bytes_facts hne hP
      refine ⟨σ, ?_, replaces_same hP, rfl⟩
      have hload := loadNat_eq (arg := arg) (a := a) hn hmem hb hrd
      rw [hlen] at hload
      cases t <;> cases packed <;>
        simp_all [Exec.instr, Exec.i32, loadWidth, loadValue])
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold WasmLogic.memBytes
  iintro ⟨Hc, Hb, HΦ⟩
  iapply key
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hb]
  · iexact Hb
  · iexact HΦ

theorem mwpi_store (t : NumType) (bits : Option Nat) (arg : MemArg) (a : UInt32) (v : Value)
    (n : Nat) (old : List UInt8) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : old.length = storeWidth t bits) (hne : old ≠ []) :
    credits Cg (cfg.regularOpCost + R) ∗ n ↦[wms][ a.toNat + arg.offset ] old ∗
      ▷ (n ↦[wms][ a.toNat + arg.offset ] storeBytes v old.length -∗ credits Cg R -∗
          Φ.normal vs f)
      ⊢ mwpi cfg lim d f (vs ++ [.i32 a, v]) [.store t bits arg] Φ := by
  have key := mwpi_instr (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f)
    (vs := vs ++ [.i32 a, v]) (Cg := Cg) (R := R)
    (.store t bits arg) rfl vs f.locals []
    (byteCells n (a.toNat + arg.offset) old)
    (byteCells n (a.toNat + arg.offset) (storeBytes v old.length))
    (by simp) (byteCells_plain _ _ _) (byteCells_plain _ _ _)
    (byteCells_nodup _ _ _) (byteCells_nodup _ _ _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, hwf, hb, _⟩ := bytes_facts hne hP
      let g := fun i => UInt8.ofNat (storeRaw v >>> (8 * i))
      refine ⟨{ σ with mems := σ.mems.set! n (mem.writeRun (a.toNat + arg.offset) old.length g) },
        ?_, replaces_write hmem hwf hb g, rfl⟩
      have hstore : Exec.storeNat σ f.mi arg a old.length (storeRaw v) =
          some { σ with mems := σ.mems.set! n (mem.writeRun (a.toNat + arg.offset) old.length g) } := by
        simp [Exec.storeNat, memOf_eq hn hmem, Memory.writeNat_eq hb, Store.setMemOf, hn, g]
      rw [hlen] at hstore
      cases bits <;> cases v <;>
        simp_all [Exec.instr, Exec.storeEffect, Exec.i32, storeWidth, storeRaw])
    (by
      intro σ _ _ _ l hq hp
      rw [lookup_byteCells] at hq hp
      simp only [storeBytes, List.length_map, List.length_range] at hq
      split at hp
      · cases hp
      · rename_i hc; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold WasmLogic.memBytes
  iintro ⟨Hc, Hb, HΦ⟩
  iapply key
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hb]
  · iexact Hb
  · iexact HΦ

theorem mwpi_memory_size (n len : Nat) (hn : f.mi.memAddrs[0]? = some n) :
    credits Cg (cfg.regularOpCost + R) ∗ n ↦[wmlength] len ∗
      ▷ (n ↦[wmlength] len -∗ credits Cg R -∗
          Φ.normal (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f)
      ⊢ mwpi cfg lim d f vs [.memory_size] Φ := by
  have key := mwpi_instr (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (vs := vs)
    (Cg := Cg) (R := R)
    .memory_size rfl (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f.locals []
    [(Loc.memLength n, .memLength len)] [(Loc.memLength n, .memLength len)]
    (by simp) (by simp [isPlain, Loc.memLength]) (by simp [isPlain, Loc.memLength])
    (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, _, hlen⟩ := memLength_facts (hP _ List.mem_cons_self)
      refine ⟨σ, ?_, replaces_same hP, rfl⟩
      simp [Exec.instr, memOf_eq hn hmem, size_eq_div, hlen])
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold memLength
  iintro ⟨Hc, Hl, HΦ⟩
  iapply key
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hl]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hl]
    · iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro HQ Hc
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    iapply HΦ $$ HQ
    iexact Hc

theorem mwpi_global_get (g a : Nat) (gi : GlobalInst) (ha : f.mi.globalAddrs[g]? = some a) :
    credits Cg (cfg.regularOpCost + R) ∗ a ↦[wg] gi ∗
      ▷ (a ↦[wg] gi -∗ credits Cg R -∗ Φ.normal (vs ++ [gi.value]) f)
      ⊢ mwpi cfg lim d f vs [.global_get g] Φ := by
  have key := mwpi_instr (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (vs := vs)
    (Cg := Cg) (R := R)
    (.global_get g) rfl (vs ++ [gi.value]) f.locals [] [(Loc.global a, .global gi)]
    [(Loc.global a, .global gi)] (by simp) (by simp [isPlain, Loc.global])
    (by simp [isPlain, Loc.global]) (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      have hg := global_facts (hP _ List.mem_cons_self)
      refine ⟨σ, ?_, replaces_same hP, rfl⟩
      simp [Exec.instr, getElem!_def, ha, hg])
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold globalPt
  iintro ⟨Hc, Hg, HΦ⟩
  iapply key
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hg]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hg]
    · iexact Hg
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro HQ Hc
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    iapply HΦ $$ HQ
    iexact Hc

theorem mwpi_global_set (g a : Nat) (gi : GlobalInst) (v : Value)
    (ha : f.mi.globalAddrs[g]? = some a) :
    credits Cg (cfg.regularOpCost + R) ∗ a ↦[wg] gi ∗
      ▷ (a ↦[wg] { gi with value := v } -∗ credits Cg R -∗ Φ.normal vs f)
      ⊢ mwpi cfg lim d f (vs ++ [v]) [.global_set g] Φ := by
  have key := mwpi_instr (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (vs := vs ++ [v])
    (Cg := Cg) (R := R)
    (.global_set g) rfl vs f.locals [] [(Loc.global a, .global gi)]
    [(Loc.global a, .global { gi with value := v })] (by simp) (by simp [isPlain, Loc.global])
    (by simp [isPlain, Loc.global]) (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      have hg := global_facts (hP _ List.mem_cons_self)
      refine ⟨{ σ with globals := σ.globals.modify a ({ · with value := v }) }, ?_, ?_, rfl⟩
      · simp [Exec.instr, getElem!_def, ha]
      · intro ⟨k, b, i⟩
        rw [lookup_modifyGlobal, lookup_cons_pair, lookup_cons_pair]
        simp only [Loc.global, Prod.mk.injEq, List.lookup_nil]
        by_cases h : k = 2 ∧ b = a ∧ i = 0
        · obtain ⟨rfl, rfl, rfl⟩ := h
          simp [hg]
        · simp [h])
    (by intro σ _ _ _ l hq hp; rw [lookup_cons_pair] at hq hp; split at hq <;> simp_all)
  simp only [Frame.withLocals_self] at key
  unfold globalPt
  iintro ⟨Hc, Hg, HΦ⟩
  iapply key
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hg]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hg]
    · iexact Hg
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro HQ Hc
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    iapply HΦ $$ HQ
    iexact Hc

end NearLogic
