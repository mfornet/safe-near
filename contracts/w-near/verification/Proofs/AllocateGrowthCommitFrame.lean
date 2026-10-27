import Proofs.AllocateGrowthCommit
import Proofs.AllocateSearchGasCost

/-! Original-memory shape, exact sequential memory and gas for growth stores. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
attribute [local irreducible] writeI32 writeI64

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih

/-- Growth initialization writes only its twelve-byte header interval. -/
theorem freshMemory_spec (memory : Memory) (header bytes : UInt32)
    (hw : memory.wf) (hb : header.toNat+12≤memory.byteSize) :
    (freshMemory memory header bytes).wf ∧
    (freshMemory memory header bytes).byteSize=memory.byteSize ∧
    (freshMemory memory header bytes).max=memory.max ∧
    ∀ j, (j<header.toNat ∨ header.toNat+12≤j) →
      (freshMemory memory header bytes).read8 j=memory.read8 j := by
  have a := writeI64_spec memory header.toNat 0 hw (by omega)
  have b := writeI32_spec (writeI64 memory header.toNat 0) (header.toNat+8) 0 a.1 (by rw [a.2.1]; omega)
  have c := writeI32_spec (writeI32 (writeI64 memory header.toNat 0) (header.toNat+8) 0)
    header.toNat ((header+bytes)|||2) b.1 (by rw [b.2.1,a.2.1]; omega)
  refine ⟨c.1,c.2.1.trans (b.2.1.trans a.2.1),c.2.2.1.trans (b.2.2.1.trans a.2.2.1),?_⟩
  intro j hj
  rw [show (freshMemory memory header bytes).read8 j=_ from c.2.2.2 j,b.2.2.2 j,a.2.2.2 j]
  simp only [show ¬(header.toNat≤j ∧ j<header.toNat+4) by omega,
    show ¬(header.toNat+8≤j ∧ j<header.toNat+8+4) by omega,
    show ¬(header.toNat≤j ∧ j<header.toNat+8) by omega,ite_false]

theorem freshStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (header bytes : UInt32)
    (hm : s.mems[index]?=some memory) :
    (freshStore s op index memory header bytes).mems[index]?=some (freshMemory memory header bytes) := by
  have a := storeI64_memory (paid s op 6) index header.toNat memory 0 (by simpa only [paid_mems] using hm)
  have b := storeI32_memory (paid (storeI64 (paid s op 6) index header.toNat memory 0) op 5) index
    (header.toNat+8) (writeI64 memory header.toNat 0) 0 (by simpa only [paid_mems] using a)
  apply storeI32_memory
  simpa only [paid_mems] using b

theorem recordMemory_spec (memory : Memory) (record header : UInt32)
    (hw : memory.wf) (hb : record.toNat+8≤memory.byteSize) :
    (recordMemory memory record header).wf ∧
    (recordMemory memory record header).byteSize=memory.byteSize ∧
    (recordMemory memory record header).max=memory.max ∧
    ∀ j, (j<record.toNat ∨ record.toNat+8≤j) →
      (recordMemory memory record header).read8 j=memory.read8 j := by
  have a := writeI32_spec memory (record.toNat+4) header hw (by omega)
  have b := writeI32_spec (writeI32 memory (record.toNat+4) header) record.toNat 0 a.1 (by rw [a.2.1]; omega)
  refine ⟨b.1,b.2.1.trans a.2.1,b.2.2.1.trans a.2.2.1,?_⟩
  intro j hj
  rw [show (recordMemory memory record header).read8 j=_ from b.2.2.2 j,a.2.2.2 j]
  simp only [show ¬(record.toNat≤j ∧ j<record.toNat+4) by omega,
    show ¬(record.toNat+4≤j ∧ j<record.toNat+4+4) by omega,ite_false]

theorem recordStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (record header : UInt32)
    (hm : s.mems[index]?=some memory) :
    (recordStore s op index memory record header).mems[index]?=some (recordMemory memory record header) := by
  have a := storeI32_memory (paid s op 3) index (record.toNat+4) memory header (by simpa only [paid_mems] using hm)
  simp only [recordStore,paid_mems]
  apply storeI32_memory
  simpa only [paid_mems] using a

private theorem units_store32 (s : Store NearState) (op n index address : Nat) (memory : Memory) (v : UInt32) :
    GasUnits s (storeI32 (paid s op n) index address memory v) op n :=
  (gasUnits_paid s op n).host_eq rfl
private theorem units_store64 (s : Store NearState) (op n index address : Nat) (memory : Memory) (v : UInt64) :
    GasUnits s (storeI64 (paid s op n) index address memory v) op n :=
  (gasUnits_paid s op n).host_eq rfl

theorem freshStore_gas (s : Store NearState) (op index : Nat) (memory : Memory) (header bytes : UInt32) :
    GasUnits s (freshStore s op index memory header bytes) op 18 := by
  have a := units_store64 s op 6 index header.toNat memory 0
  have b := a.trans (units_store32 (storeI64 (paid s op 6) index header.toNat memory 0) op 5 index
    (header.toNat+8) (writeI64 memory header.toNat 0) 0)
  exact b.trans (units_store32 _ op 7 index header.toNat _ ((header+bytes)|||2))

theorem recordStore_gas (s : Store NearState) (op index : Nat) (memory : Memory) (record header : UInt32) :
    GasUnits s (recordStore s op index memory record header) op 7 := by
  have a := units_store32 s op 3 index (record.toNat+4) memory header
  have b := a.trans (units_store32 _ op 3 index record.toNat (writeI32 memory (record.toNat+4) header) 0)
  exact b.trans (gasUnits_paid _ op 1)

private def hostView (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem hostView_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    hostView seed (paid s op n).host=hostView seed s.host := by
  induction n with | zero => rfl | succ n ih => exact ih

private def codeView (s : Store NearState) := (s.funcs,s.modules,s.globals,s.tables)
private theorem codeView_paid (s : Store NearState) (op n : Nat) : codeView (paid s op n)=codeView s := by
  induction n with | zero => rfl | succ n ih => exact ih

private theorem codeView_store32 (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) :
    codeView (storeI32 s index address memory v)=codeView s := rfl
private theorem codeView_store64 (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt64) :
    codeView (storeI64 s index address memory v)=codeView s := rfl

theorem freshStore_frame (s : Store NearState) (op index : Nat) (memory : Memory) (header bytes : UInt32) :
    (freshStore s op index memory header bytes).funcs=s.funcs ∧
    (freshStore s op index memory header bytes).modules=s.modules ∧
    (freshStore s op index memory header bytes).globals=s.globals ∧
    (freshStore s op index memory header bytes).tables=s.tables ∧
    {(freshStore s op index memory header bytes).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have hcode : codeView (freshStore s op index memory header bytes)=codeView s := by
    simp only [freshStore,codeView_store32,codeView_store64,codeView_paid]
  have host : hostView s.host (freshStore s op index memory header bytes).host=hostView s.host s.host := by
    simp only [freshStore,storeI32_host,storeI64_host,hostView_paid]
  simp only [codeView,Prod.mk.injEq] at hcode
  exact ⟨hcode.1,hcode.2.1,hcode.2.2.1,hcode.2.2.2,host⟩

theorem recordStore_frame (s : Store NearState) (op index : Nat) (memory : Memory) (record header : UInt32) :
    (recordStore s op index memory record header).funcs=s.funcs ∧
    (recordStore s op index memory record header).modules=s.modules ∧
    (recordStore s op index memory record header).globals=s.globals ∧
    (recordStore s op index memory record header).tables=s.tables ∧
    {(recordStore s op index memory record header).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have hcode : codeView (recordStore s op index memory record header)=codeView s := by
    simp only [recordStore,codeView_store32,codeView_paid]
  have host : hostView s.host (recordStore s op index memory record header).host=hostView s.host s.host := by
    simp only [recordStore,storeI32_host,hostView_paid]
  simp only [codeView,Prod.mk.injEq] at hcode
  exact ⟨hcode.1,hcode.2.1,hcode.2.2.1,hcode.2.2.2,host⟩
end WNear.Proofs.AllocateGrowth
