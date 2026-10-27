import Wasm.LinkTableLookup
import Wasm.MemoryLemmas

/-! Selected-byte facts for actual active-data initialization. Byte payloads
remain symbolic; only the selected indices need concrete certificates. -/
namespace Wasm.Link
set_option maxRecDepth 4096

/-- The memory representation invariant needed for byte-write semantics. -/
def MemoriesWF (s : Store H) : Prop := ∀ m ∈ s.mems, m.wf

theorem memory_new_wf (min : Nat) (max : Option Nat) : (Memory.new min max).wf := by
  apply (Memory.wf_iff _).mpr
  intro i hi
  left
  simp [Memory.new]

/-- Successful actual byte writes preserve representation and install each
selected byte, without expanding the source byte array. -/
theorem writeBytes_read (m : Memory) (hwf : m.wf) (offset : Nat) (bytes : ByteArray)
    (written : Memory) (h : m.writeBytes offset bytes = some written) :
    written.wf ∧ written.byteSize = m.byteSize ∧
      ∀ i < bytes.size, written.read8 (offset + i) = bytes[i]! := by
  by_cases hb : offset + bytes.size ≤ m.byteSize
  · simp only [Memory.writeBytes, Memory.inBounds, hb, decide_true, ite_true,
      Option.some.injEq] at h
    subst written
    have hs := Memory.writeRun_spec hwf hb (fun i => bytes[i]!)
    refine ⟨hs.1, hs.2.1, fun i hi => ?_⟩
    erw [hs.2.2.2]
    have hr : offset ≤ offset + i ∧ offset + i < offset + bytes.size := by omega
    simp only [hr, true_and, ite_true, Nat.add_sub_cancel_left]
  · simp only [Memory.writeBytes, Memory.inBounds, hb, decide_false] at h
    cases h

private theorem fold_mems (xs : List α)
    (step : Store H × Array Nat → α → Store H × Array Nat)
    (hf : ∀ s a x, (step (s, a) x).1.mems = s.mems) (s : Store H) (a : Array Nat) :
    (xs.foldl step (s, a)).1.mems = s.mems := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem allocFuncs_mems (s : Store H) (types : Array FuncType) (inst : Nat) (fs : List Func) :
    (allocFuncs s types inst fs).1.mems = s.mems := by
  apply fold_mems
  intros
  rfl

theorem allocTables_mems (s : Store H) (ts : List Table) :
    (allocTables s ts).1.mems = s.mems := by rw [allocTables_layout]

theorem allocMems_wf (s : Store H) (ms : List Mem) (hs : MemoriesWF s) :
    MemoriesWF (allocMems s ms).1 := by
  suffices aux : ∀ (s : Store H) (a : Array Nat), MemoriesWF s →
      MemoriesWF (ms.foldl (fun (s, a) mem =>
        let (s, addr) := s.allocMem (Memory.new mem.type.limits.min mem.type.limits.max)
        (s, a.push addr)) (s, a)).1 from aux s #[] hs
  intro s a hs
  induction ms generalizing s a with
  | nil => exact hs
  | cons mem ms ih =>
    apply ih
    intro m hm
    simp only [Array.mem_push] at hm
    rcases hm with hm | rfl
    · exact hs m hm
    · exact memory_new_wf _ _

theorem allocGlobals_mems (s : Store H) (inst : ModuleInst) (xs : List Global)
    {after : Store H} {result : ModuleInst} (h : allocGlobals s inst xs = .ok (after, result)) :
    after.mems = s.mems := by
  induction xs generalizing s inst with
  | nil =>
    simp only [allocGlobals, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ rfl
  | cons g xs ih =>
    simp only [allocGlobals] at h
    split at h
    · cases h
    · have hr := ih _ _ h
      exact hr

theorem allocElems_mems (s : Store H) (inst : ModuleInst) (xs : List Elem)
    {after : Store H} {addrs : Array Nat} (h : allocElems s inst xs = .ok (after, addrs)) :
    after.mems = s.mems := by
  induction xs generalizing s addrs with
  | nil =>
    simp only [allocElems, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ rfl
  | cons e xs ih =>
    simp only [allocElems] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i v refs he pair rest addresses hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hm := ih _ hr
        exact hm

theorem allocDatas_mems (s : Store H) (ds : List Data) :
    (allocDatas s ds).1.mems = s.mems := by
  apply fold_mems
  intros
  rfl

theorem initElem_mems (s : Store H) (inst : ModuleInst) (n : Nat) (e : Elem)
    {after : Store H} (h : initElem s inst n e = .ok after) : after.mems = s.mems := by
  unfold initElem at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        split at h
        · cases h
        · cases h; rfl
  · cases h; rfl
  · cases h; rfl

theorem initElems_mems (s : Store H) (inst : ModuleInst) (xs : List (Nat × Elem))
    {after : Store H} (h : initElems s inst xs = .ok after) : after.mems = s.mems := by
  induction xs generalizing s with
  | nil => cases h; rfl
  | cons x xs ih =>
    rcases x with ⟨n, e⟩
    simp only [initElems] at h
    split at h
    · cases h
    · rename_i next hi
      exact (ih _ h).trans (initElem_mems _ _ _ _ hi)

/-- A successful active-data operation gives the actual memory address and
its exact source bytes. The index-zero selection is the linker's `memOf`. -/
theorem initData_read (s : Store H) (inst : ModuleInst) (n : Nat) (d : Data)
    (after : Store H) (offset : UInt32)
    (hmode : d.mode = .active 0 [.i32_const offset]) (hwf : MemoriesWF s)
    (h : initData s inst n d = .ok after) :
    ∃ index memory, inst.memAddrs[0]? = some index ∧ after.mems[index]? = some memory ∧
      memory.wf ∧ ∀ i < d.init.size, memory.read8 (offset.toNat + i) = d.init[i]! := by
  unfold initData at h
  rw [hmode] at h
  simp only [evalConst] at h
  cases ha : inst.memAddrs[0]? with
  | none => simp [Store.memOf, ha] at h
  | some index =>
    cases hm : s.mems[index]? with
    | none => simp [Store.memOf, ha, hm] at h
    | some memory =>
      simp [Store.memOf, ha, hm] at h
      dsimp only [Exec.i32] at h
      cases hb : memory.writeBytes offset.toNat d.init with
      | none => simp only [hb] at h; cases h
      | some written =>
        simp only [hb, Except.ok.injEq] at h
        subst after
        have hs := writeBytes_read memory (hwf memory (Array.mem_of_getElem? hm))
          offset.toNat d.init written hb
        refine ⟨index, written, rfl, ?_, hs.1, hs.2.2⟩
        simp only [Store.setMemOf, ha]
        simp only [Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hm).1]

theorem initDatas_single (s : Store H) (inst : ModuleInst) (n : Nat) (d : Data) :
    initDatas s inst [(n, d)] = initData s inst n d := by
  unfold initDatas
  cases hd : initData s inst n d <;> rfl

/-- Full successful instantiation with one active data segment yields its
selected bytes in the actual first memory. Well-formed input memories suffice;
newly allocated memories are proved well formed by the loader rules above. -/
theorem instantiateModule_single_active_data_read (s : Store H) (vm : ValidModule)
    (imports : List ExternVal) (after : Store H) (inst : ModuleInst)
    (h : instantiateModule s vm imports = .ok (after, inst))
    (d : Data) (hsingle : vm.module.datas = #[d]) (offset : UInt32)
    (hmode : d.mode = .active 0 [.i32_const offset]) (hwf : MemoriesWF s) :
    ∃ index memory, inst.memAddrs[0]? = some index ∧ after.mems[index]? = some memory ∧
      memory.wf ∧ ∀ i < d.init.size, memory.read8 (offset.toNat + i) = d.init[i]! := by
  unfold instantiateModule at h
  dsimp only at h
  have hindexed : indexed #[d] = [(0, d)] := rfl
  simp only [hsingle, hindexed, initDatas_single] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i globalsResult globalsStore globalsInst hg
        split at h
        · cases h
        · rename_i elemsResult elemsStore elemAddrs he
          split at h
          · cases h
          · rename_i initializedResult initialized hie
            split at h
            · cases h
            · rename_i finalResult final hd
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hglobals := allocGlobals_mems _ _ _ hg
              have hglobalsWF : MemoriesWF globalsStore := by
                unfold MemoriesWF
                rw [hglobals]
                apply allocMems_wf
                unfold MemoriesWF
                rw [allocTables_mems, allocFuncs_mems]
                exact hwf
              have helems := allocElems_mems _ _ _ he
              have helemsWF : MemoriesWF elemsStore := by
                unfold MemoriesWF
                rw [helems]
                exact hglobalsWF
              have hinit := initElems_mems _ _ _ hie
              have hinitWF : MemoriesWF initialized := by
                unfold MemoriesWF
                rw [hinit]
                change ∀ m ∈ (allocDatas elemsStore #[d].toList).1.mems, m.wf
                rw [allocDatas_mems]
                exact helemsWF
              exact initData_read _ _ 0 d _ offset hmode hinitWF hd

end Wasm.Link
