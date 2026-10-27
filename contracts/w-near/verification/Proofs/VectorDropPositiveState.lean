import Proofs.VectorDropEntryPrefix

/-! Original functional data and exact intermediate states of positive vector
 destruction. Heap deallocation is a separate, later execution phase. -/
namespace WNear.Proofs.VectorDropPositive
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
open WNear.Proofs.VectorDrop

structure Layout where
  mi : ModuleInst
  memoryIndex : Nat
  memory : Memory
  vector : UInt32
  address778 : Nat
  address747 : Nat
  address777 : Nat
  address311 : Nat

def pointer (p : Layout) := readI32 p.memory p.vector.toNat
def capacity (p : Layout) := readI32 p.memory (p.vector.toNat + 4)
def arguments (p : Layout) : List Value := [.i32 (pointer p), .i32 (capacity p), .i32 1]
def vectorLeaf (inst height : Nat) (p : Layout) := vectorFrame inst height p.vector
def vectorBlocked (inst height : Nat) (p : Layout) := emptyBlockFrame (capacityFrame (vectorLeaf inst height p) (capacity p)) height []
def capacityLeaf (inst height : Nat) (p : Layout) := tripleFrame inst height (pointer p) (capacity p) 1
def capacityBlocked (inst height : Nat) (p : Layout) := emptyBlockFrame (capacityLeaf inst height p) height []
def forwardLeaf (inst height : Nat) (p : Layout) := tripleFrame inst height (pointer p) (capacity p) 1

def before747 (s : Store NearState) (op : Nat) := paid (entered (paid s op 1) op) op 1
def before777 (s : Store NearState) (op : Nat) := paid (entered (before747 s op) op) op 9
def before311 (s : Store NearState) (op : Nat) := paid (tripleEntry (before777 s op) op) op 6
def before237 (s : Store NearState) (op : Nat) := paid (tripleEntry (before311 s op) op) op 3

/-- Code and native memory facts in the original body store. No allocator
execution or future heap state is assumed. -/
structure Ready (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  module : s.modules[inst]? = some p.mi
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  index778 : p.mi.funcAddrs[778]? = some p.address778
  function778 : s.funcs[p.address778]? = some (.wasm WNear.Binary.VectorDrop.signature inst WNear.Binary.VectorDrop.function778)
  index747 : p.mi.funcAddrs[747]? = some p.address747
  function747 : s.funcs[p.address747]? = some (.wasm WNear.Binary.VectorDrop.signature inst WNear.Binary.VectorDrop.function747)
  index777 : p.mi.funcAddrs[777]? = some p.address777
  function777 : s.funcs[p.address777]? = some (.wasm WNear.Binary.VectorDrop.tripleSignature inst WNear.Binary.VectorDrop.function777)
  index311 : p.mi.funcAddrs[311]? = some p.address311
  function311 : s.funcs[p.address311]? = some (.wasm WNear.Binary.VectorDrop.tripleSignature inst WNear.Binary.VectorDrop.function311)
  bound : p.vector.toNat + 8 ≤ p.memory.byteSize
  positive : capacity p ≠ 0



theorem before747_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (12 * op + rest)) : (before747 s op).host.gas.Credits rest := by
  have c1 := WNear.Proofs.StorePairCaller.paid_credits s op 1 (11 * op + rest) (hc.mono (by omega))
  have c2 := entered_credits (paid s op 1) op (op + rest) (c1.mono (by omega))
  exact WNear.Proofs.StorePairCaller.paid_credits (entered (paid s op 1) op) op 1 rest (c2.mono (by omega))

theorem before777_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (31 * op + rest)) : (before777 s op).host.gas.Credits rest := by
  have c1 := before747_credits s op (19 * op + rest) (hc.mono (by omega))
  have c2 := entered_credits (before747 s op) op (9 * op + rest) (c1.mono (by omega))
  exact WNear.Proofs.StorePairCaller.paid_credits (entered (before747 s op) op) op 9 rest c2

theorem before311_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (48 * op + rest)) : (before311 s op).host.gas.Credits rest := by
  have c1 := before777_credits s op (17 * op + rest) (hc.mono (by omega))
  have c2 := tripleEntry_credits (before777 s op) op (6 * op + rest) (c1.mono (by omega))
  exact WNear.Proofs.StorePairCaller.paid_credits (tripleEntry (before777 s op) op) op 6 rest c2

theorem before237_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (62 * op + rest)) : (before237 s op).host.gas.Credits rest := by
  have c1 := before311_credits s op (14 * op + rest) (hc.mono (by omega))
  have c2 := tripleEntry_credits (before311 s op) op (3 * op + rest) (c1.mono (by omega))
  exact WNear.Proofs.StorePairCaller.paid_credits (tripleEntry (before311 s op) op) op 3 rest c2

/-- Until the allocator call all runtime arrays and all functional host fields
remain those in the original body store. -/
theorem before237_resources (s : Store NearState) (op : Nat) :
    {before237 s op with host := s.host} = s := by
  simp only [before237, before311, before777, before747, paid, entered, tripleEntry, chargedStore]

theorem before237_functional_host (s : Store NearState) (op : Nat) :
    {(before237 s op).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [before237, before311, before777, before747, paid, entered, tripleEntry, chargedStore, chargeHost]
end WNear.Proofs.VectorDropPositive
