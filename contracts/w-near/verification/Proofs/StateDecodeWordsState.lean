import Proofs.StateDecodeWordsSteps

/-! Exact accepted byte-reader effects, retaining sequential source/output aliases. -/
namespace WNear.Proofs.StateDecodeWords
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

def copiedMemory (wide : Bool) (memory : Memory) (out source : UInt32) :=
  if wide then writeI64 (lowMemory memory out source) (out+9).toNat (readI64 (lowMemory memory out source) (source+8).toNat)
  else lowMemory memory out source
def finalMemory (wide : Bool) (memory : Memory) (out source : UInt32) := writeByte (copiedMemory wide memory out source) out.toNat 0
def copyAfter (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  if wide then highStore (lowStore s op index memory out source) op index (lowMemory memory out source) out source
  else lowStore s op index memory out source
def after (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :=
  statusStore (paid (copyAfter wide (paid s op 6) op index memory out source) op 2) op index (copiedMemory wide memory out source) out
def copyCost (wide : Bool) : Nat := if wide then 12 else 4
def bodyCost (wide : Bool) : Nat := copyCost wide+11
def bodySteps (wide : Bool) : Nat := bodyCost wide+2

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem copyAfter_modules (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    (copyAfter wide s op index memory out source).modules=s.modules := by
  cases wide <;> simp only [copyAfter,Bool.false_eq_true,ite_false,ite_true,highStore,lowStore,storeI64_modules,modules_paid]

private theorem lowStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32)
    (hm : s.mems[index]?=some memory) :
    (lowStore s op index memory out source).mems[index]?=some (lowMemory memory out source) := by
  have mp : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact hm
  exact storeI64_memory (paid s op 4) index (out.toNat+1) memory (readI64 memory source.toNat) mp
private theorem highStore_memory (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32)
    (hm : s.mems[index]?=some memory) :
    (highStore s op index memory out source).mems[index]?=some (writeI64 memory (out+9).toNat (readI64 memory (source+8).toNat)) := by
  have mp : (paid s op 8).mems[index]?=some memory := by rw [mems_paid];exact hm
  exact storeI64_memory (paid s op 8) index (out+9).toNat memory (readI64 memory (source+8).toNat) mp

theorem copyAfter_memory (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32)
    (hm : s.mems[index]?=some memory) :
    (copyAfter wide s op index memory out source).mems[index]?=some (copiedMemory wide memory out source) := by
  cases wide
  · simp only [copyAfter,copiedMemory,Bool.false_eq_true,ite_false]
    exact lowStore_memory s op index memory out source hm
  · simp only [copyAfter,copiedMemory,ite_true]
    exact highStore_memory (lowStore s op index memory out source) op index (lowMemory memory out source) out source
      (lowStore_memory s op index memory out source hm)

theorem copyAfter_credits (wide : Bool) (s : Store NearState) (op index rest : Nat) (memory : Memory) (out source : UInt32)
    (hc : s.host.gas.Credits (copyCost wide*op+rest)) :
    (copyAfter wide s op index memory out source).host.gas.Credits rest := by
  cases wide
  · exact paid_credits s op 4 rest hc
  · have h := paid_credits s op 4 (8*op+rest) (hc.mono (by simp only [copyCost,ite_true];omega))
    exact paid_credits (lowStore s op index memory out source) op 8 rest h

theorem copiedMemory_spec (wide : Bool) (memory : Memory) (out source : UInt32)
    (hwf : memory.wf) (ho : out.toNat+17≤memory.byteSize)
    (ha : (out+9).toNat=out.toNat+9) :
    (copiedMemory wide memory out source).wf ∧ (copiedMemory wide memory out source).byteSize=memory.byteSize ∧
    (copiedMemory wide memory out source).max=memory.max := by
  have low := writeI64_spec memory (out.toNat+1) (readI64 memory source.toNat) hwf (by omega)
  cases wide
  · exact ⟨low.1,low.2.1,low.2.2.1⟩
  · have b : (out+9).toNat+8≤(lowMemory memory out source).byteSize := by change _≤(writeI64 memory _ _).byteSize;rw [low.2.1,ha];omega
    have high := writeI64_spec (lowMemory memory out source) (out+9).toNat (readI64 (lowMemory memory out source) (source+8).toNat) low.1 b
    exact ⟨high.1,high.2.1.trans low.2.1,high.2.2.1.trans low.2.2.1⟩
end WNear.Proofs.StateDecodeWords
