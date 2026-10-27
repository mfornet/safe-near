import Proofs.AllocateGrowthPhaseFrame
import Proofs.PanicAllocateReadback

/-! Exact memory and functional resource effects of successful allocator growth. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] rounded beforeGrowth growthStore growthAfter bytesAfter prepared sized grownPhase pageChecked after569 converted committed after freshStore recordStore writeI32 writeI64

theorem committed_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (committed cfg s p).mems[p.memoryIndex]?=some (committedMemory p) := by
  simpa only [committed,committedMemory] using freshStore_memory (converted cfg s p) cfg.regularOpCost p.memoryIndex p.grown (header p) (blockBytes p)
    (converted_memory cfg s p hm)

theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  simpa only [after,finalMemory] using recordStore_memory (committed cfg s p) cfg.regularOpCost p.memoryIndex (committedMemory p) p.record (header p)
    (committed_memory cfg s p hm)

theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize+(delta p).toNat*65536 ∧
    (finalMemory p).max=p.memory.max := by
  have grow := hn.grown_spec p
  have fresh := freshMemory_spec p.grown (header p) (blockBytes p) grow.1 grow.2.2.1
  have recordBound : p.record.toNat+8≤(committedMemory p).byteSize := by
    change p.record.toNat+8≤(freshMemory p.grown (header p) (blockBytes p)).byteSize
    rw [fresh.2.1]
    exact grow.2.2.2
  have record := recordMemory_spec (committedMemory p) p.record (header p) fresh.1 recordBound
  have maxGrow := (Memory.grow_spec hn.wf hn.grow).2.2.1
  exact ⟨record.1,record.2.1.trans (fresh.2.1.trans grow.2.1),record.2.2.1.trans (fresh.2.2.1.trans maxGrow)⟩

theorem finalMemory_record (p : Layout) (hn : Native p) :
    readI32 (finalMemory p) p.record.toNat=0 ∧
    readI32 (finalMemory p) (p.record.toNat+4)=header p := by
  have grow := hn.grown_spec p
  have fresh := freshMemory_spec p.grown (header p) (blockBytes p) grow.1 grow.2.2.1
  have bound : p.record.toNat+8≤(committedMemory p).byteSize := by
    change p.record.toNat+8≤(freshMemory p.grown (header p) (blockBytes p)).byteSize
    rw [fresh.2.1]
    exact grow.2.2.2
  have first := writeI32_spec (committedMemory p) (p.record.toNat+4) (header p) fresh.1 (by omega)
  have secondBound : p.record.toNat+4≤(writeI32 (committedMemory p) (p.record.toNat+4) (header p)).byteSize := by rw [first.2.1];omega
  constructor
  · exact PanicAllocateReadback.read_write_self _ _ 0 first.1 secondBound
  · have framed := PanicAllocateReadback.read_write_frame
      (writeI32 (committedMemory p) (p.record.toNat+4) (header p)) (p.record.toNat+4) p.record.toNat 0
      first.1 secondBound (Or.inr (by omega))
    exact framed.trans (PanicAllocateReadback.read_write_self _ _ _ fresh.1 (by omega))

theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).funcs=s.funcs ∧ (after cfg s p).modules=s.modules ∧
    (after cfg s p).globals=s.globals ∧ (after cfg s p).tables=s.tables := by
  have a := converted_fields cfg s p
  have b := freshStore_frame (converted cfg s p) cfg.regularOpCost p.memoryIndex p.grown (header p) (blockBytes p)
  have c := recordStore_frame (committed cfg s p) cfg.regularOpCost p.memoryIndex (committedMemory p) p.record (header p)
  simp only [after,committed] at c ⊢
  exact ⟨c.1.trans (b.1.trans a.1),c.2.1.trans (b.2.1.trans a.2.1),
    c.2.2.1.trans (b.2.2.1.trans a.2.2.2.1),c.2.2.2.1.trans (b.2.2.2.1.trans a.2.2.2.2)⟩

private def hv (seed : NearState) (s : Store NearState) := {s.host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem hv_paid (seed : NearState) (s : Store NearState) (op n : Nat) : hv seed (paid s op n)=hv seed s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem hv_charge (seed : NearState) (s : Store NearState) (cost : Nat) : hv seed (chargedStore s cost)=hv seed s := rfl
private theorem hv_store32 (seed : NearState) (s : Store NearState) (index address : Nat) (m : Memory) (v : UInt32) :
    hv seed (storeI32 s index address m v)=hv seed s := rfl
private theorem hv_store64 (seed : NearState) (s : Store NearState) (index address : Nat) (m : Memory) (v : UInt64) :
    hv seed (storeI64 s index address m v)=hv seed s := rfl
private theorem hv_grown (seed : NearState) (s : Store NearState) (index : Nat) (m : Memory) :
    hv seed (grownStore s index m)=hv seed s := rfl

private theorem hv_rounded (seed : NearState) (s : Store NearState) (op : Nat) : hv seed (rounded s op)=hv seed s := by
  simp only [rounded,after569,bodyAfter569,entered569,DeallocateAlign.after568,DeallocateAlign.entered568,hv_paid,hv_charge]
private theorem hv_prepared (seed : NearState) (s : Store NearState) (op : Nat) : hv seed (prepared s op)=hv seed s := by
  simp only [prepared,AllocateUnits.unitsAfter,AllocateUnits.entered9,hv_paid,hv_charge]
private theorem hv_bytesAfter (seed : NearState) (s : Store NearState) (op : Nat) : hv seed (bytesAfter s op)=hv seed s := by
  simp only [bytesAfter,after573,AllocateUnits.minimumAfter,AllocateUnits.entered9,hv_paid,hv_charge]
private theorem hv_fresh (seed : NearState) (s : Store NearState) (op index : Nat) (m : Memory) (header bytes : UInt32) :
    hv seed (freshStore s op index m header bytes)=hv seed s := by
  simp only [freshStore,hv_store32,hv_store64,hv_paid]
private theorem hv_record (seed : NearState) (s : Store NearState) (op index : Nat) (m : Memory) (record header : UInt32) :
    hv seed (recordStore s op index m record header)=hv seed s := by
  simp only [recordStore,hv_store32,hv_paid]
attribute [local irreducible] memoryGrowCost growPages chargedStore grownStore hv

private theorem hv_beforeGrowth (seed : NearState) (s : Store NearState) (op : Nat) : hv seed (beforeGrowth s op)=hv seed s := by
  simp only [beforeGrowth,hv_paid,hv_rounded]
private theorem hv_growthStore (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (index : Nat) (m : Memory) (bytes : UInt32) :
    hv seed (growthStore cfg s index m bytes)=hv seed s := by
  unfold growthStore
  rw [hv_grown,hv_charge,hv_beforeGrowth]
private theorem hv_growthAfter (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (index : Nat) (m : Memory) (bytes : UInt32) :
    hv seed (growthAfter cfg s index m bytes)=hv seed s := by
  unfold growthAfter
  rw [hv_paid,hv_growthStore]

theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h : hv s.host (after cfg s p)=hv s.host s := by
    simp only [after,hv_record,committed,hv_fresh,converted,hv_bytesAfter,pageChecked,hv_paid,
      grownPhase,hv_growthAfter,sized,hv_paid,hv_prepared]
  simpa only [hv] using h
end WNear.Proofs.AllocateGrowth
