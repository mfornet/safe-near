import Proofs.AllocateSkipState

/-! The actual root write derives all next-candidate native conditions. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
attribute [local irreducible] readI32 writeI32

private theorem write_read_self (memory : Memory) (address : Nat) (value : UInt32)
    (hw : memory.wf) (hb : address+4≤memory.byteSize) : readI32 (writeI32 memory address value) address=value := by
  have h := writeI32_spec memory address value hw hb
  apply ValueReturnOuterLayout.readI32_of_bytes
  intro i hi
  rw [h.2.2.2]
  have within : address≤address+i ∧ address+i<address+4 := by omega
  simp [within]
private theorem write_read_away (memory : Memory) (address other : Nat) (value : UInt32)
    (hw : memory.wf) (hb : address+4≤memory.byteSize)
    (hs : address+4≤other ∨ other+4≤address) : readI32 (writeI32 memory address value) other=readI32 memory other := by
  have h := writeI32_spec memory address value hw hb
  apply readI32_congr_bytes
  intro i hi
  rw [h.2.2.2]
  have outside : ¬ (address≤other+i ∧ other+i<address+4) := by rcases hs with h|h <;> omega
  rw [ite_eq_right outside]

 theorem nextMemory_spec (p : Layout) (hn : Native p) :
    (nextMemory p).wf ∧ (nextMemory p).byteSize=p.memory.byteSize ∧ (nextMemory p).max=p.memory.max := by
  have h := writeI32_spec p.memory p.root.toNat (next p) hn.wf hn.rootBound
  exact ⟨h.1,h.2.1,h.2.2.1⟩
 theorem nextLayout_head (p : Layout) (hn : Native p) : head (nextLayout p)=next p :=
  write_read_self p.memory p.root.toNat (next p) hn.wf hn.rootBound
 theorem nextMemory_header (p : Layout) (hn : Native p) : readI32 (nextMemory p) (next p).toNat=readI32 p.memory (next p).toNat := by
  apply write_read_away p.memory p.root.toNat (next p).toNat (next p) hn.wf hn.rootBound
  rcases hn.rootNextSep with h|h <;> omega
 theorem nextMemory_candidate (p : Layout) (hn : Native p) : readI32 (nextMemory p) ((next p).toNat+8)=readI32 p.memory ((next p).toNat+8) := by
  apply write_read_away p.memory p.root.toNat ((next p).toNat+8) (next p) hn.wf hn.rootBound
  rcases hn.rootNextSep with h|h <;> omega
 theorem nextMemory_vtable (p : Layout) (hn : Native p) : readI32 (nextMemory p) (p.vtable.toNat+16)=readI32 p.memory (p.vtable.toNat+16) :=
  write_read_away p.memory p.root.toNat (p.vtable.toNat+16) (next p) hn.wf hn.rootBound hn.rootVtableSep
 theorem next_end (p : Layout) (hn : Native p) : Allocate.endWord (nextMemory p) (next p)=Allocate.endWord p.memory (next p) := by
  simp only [Allocate.endWord,nextMemory_header p hn]

 theorem native_next (p : Layout) (hn : Native p) : AllocateSearch.Native (nextLayout p) := by
  have shape := nextMemory_spec p hn
  have he := nextLayout_head p hn
  have bound : p.root.toNat+4≤(nextMemory p).byteSize := by rw [shape.2.1];exact hn.rootBound
  refine {memoryWf:=shape.1,rootBound:=bound,headNonzero:=?_,split:=?_,endBound:=?_,headFlags:=?_,candidateFlag:=?_,vtableBound:=?_}
  · rw [he];exact hn.nextNonzero
  · rw [he]
    refine ⟨hn.split.wordsPositive,?_,?_⟩
    · change (next p).toNat+80+p.words.toNat*4≤(Allocate.endWord (nextMemory p) (next p)).toNat
      rw [next_end p hn];exact hn.split.room
    · change (Allocate.endWord (nextMemory p) (next p)).toNat≤(nextMemory p).byteSize
      rw [next_end p hn,shape.2.1];exact hn.split.endBound
  · change (Allocate.endWord (nextMemory p) (head (nextLayout p))).toNat+8≤(nextMemory p).byteSize
    rw [he,next_end p hn,shape.2.1];exact hn.endBound
  · change readI32 (nextMemory p) (head (nextLayout p)).toNat &&& 3=0
    rw [he,nextMemory_header p hn];exact hn.headFlags
  · change readI32 (nextMemory p) ((head (nextLayout p)).toNat+8) &&& 1=0
    rw [he,nextMemory_candidate p hn];exact hn.nextCandidateFlag
  · change p.vtable.toNat+20≤(nextMemory p).byteSize
    rw [shape.2.1];exact hn.vtableBound

 theorem code_next (s : Store NearState) (p : Layout) (inst : Nat) (hc : SearchCode s p inst) (hn : Native p) :
    SearchCode s (nextLayout p) inst := by
  refine {hc with callbackElement:=?_}
  change p.table.elems[(readI32 (nextMemory p) (p.vtable.toNat+16)).toNat]?=some (.func p.callbackAddress)
  rw [nextMemory_vtable p hn];exact hc.callbackElement

 theorem words_bound (p : Layout) (hn : Native p) : p.words.toNat<2^30 := by
  have room := hn.split.room
  have bound := (Allocate.endWord p.memory (next p)).toNat_lt
  omega
 theorem first_short (p : Layout) (hn : Native p) :
    Numeric.irelop32 .lt_u (DeallocateListSize.size p.memory (head p)) (p.words*4)=true := by
  have hw := words_bound p hn
  have count : (p.words*4).toNat=p.words.toNat*4 := by
    rw [UInt32.toNat_mul]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt
    omega
  change decide (DeallocateListSize.size p.memory (head p)<p.words*4)=true
  simp only [decide_eq_true_eq,UInt32.lt_iff_toNat_lt,count]
  exact hn.short
end WNear.Proofs.AllocateSkip
