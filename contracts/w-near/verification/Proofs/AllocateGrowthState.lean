import Proofs.AllocateGrowthPreparation
import Proofs.AllocateGrowthSizing
import Proofs.AllocateGrowthAttempt
import Proofs.AllocateGrowthMiddle
import Proofs.AllocateGrowthCommitFrame

/-! Original structural resources and native data for the real successful f577 path. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

structure Layout where
  mi : ModuleInst
  memoryIndex : Nat
  memory : Memory
  grown : Memory
  record : UInt32
  words : UInt32
  alignment : UInt32
  address568 : Nat
  address569 : Nat
  address572 : Nat
  address573 : Nat
  address574 : Nat

def units (p : Layout) := p.words <<< (2 : UInt32)
def requested (p : Layout) := paddedSize (units p) p.alignment
def delta (p : Layout) := growPages (requested p)
def oldPages (p : Layout) := UInt32.ofNat p.memory.size
def header (p : Layout) := pageBytes (oldPages p)
def blockBytes (p : Layout) := pageBytes (delta p)
def committedMemory (p : Layout) := freshMemory p.grown (header p) (blockBytes p)
def finalMemory (p : Layout) := recordMemory (committedMemory p) p.record (header p)

def sized (s : Store NearState) (op : Nat) := paid (prepared s op) op 29
def grownPhase (cfg : WasmConfig) (s : Store NearState) (p : Layout) := growthAfter cfg (sized s cfg.regularOpCost) p.memoryIndex p.grown (requested p)
def pageChecked (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (grownPhase cfg s p) cfg.regularOpCost 6
def converted (cfg : WasmConfig) (s : Store NearState) (p : Layout) := bytesAfter (pageChecked cfg s p) cfg.regularOpCost
def committed (cfg : WasmConfig) (s : Store NearState) (p : Layout) := freshStore (converted cfg s p) cfg.regularOpCost p.memoryIndex p.grown (header p) (blockBytes p)
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) := recordStore (committed cfg s p) cfg.regularOpCost p.memoryIndex (committedMemory p) p.record (header p)

structure Native (p : Layout) : Prop where
  wordsBound : p.words.toNat<2^30
  alignAdd : Numeric.irelop32 .lt_u (alignPlus p.alignment) p.alignment=false
  alignMask : alignPlus p.alignment &&& 536870911=alignPlus p.alignment
  padAdd : Numeric.irelop32 .lt_u (requested p) (chosenSize (units p) p.alignment)=false
  roundBound : (requested p).toNat+65536<2^32
  pagesBound : (delta p).toNat<65536
  pagesPositive : 0<(delta p).toNat
  oldPagesBound : p.memory.size<65536
  wf : p.memory.wf
  grow : p.memory.grow (delta p).toNat=some p.grown
  recordBound : p.record.toNat+8≤p.memory.byteSize

structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  module : s.modules[inst]?=some p.mi
  memoryIndex : p.mi.memAddrs[0]?=some p.memoryIndex
  index568 : p.mi.funcAddrs[568]?=some p.address568
  function568 : s.funcs[p.address568]?=some (.wasm WNear.Binary.DeallocateAlign.signature568 inst WNear.Binary.DeallocateAlign.function568)
  index569 : p.mi.funcAddrs[569]?=some p.address569
  function569 : s.funcs[p.address569]?=some (.wasm WNear.Binary.AllocateGrowth.signature569 inst WNear.Binary.AllocateGrowth.function569)
  index572 : p.mi.funcAddrs[572]?=some p.address572
  function572 : s.funcs[p.address572]?=some (.wasm WNear.Binary.AllocateUnits.unitsSignature inst WNear.Binary.AllocateUnits.unitsFunction)
  index573 : p.mi.funcAddrs[573]?=some p.address573
  function573 : s.funcs[p.address573]?=some (.wasm WNear.Binary.AllocateGrowth.signature573 inst WNear.Binary.AllocateGrowth.function573)
  index574 : p.mi.funcAddrs[574]?=some p.address574
  function574 : s.funcs[p.address574]?=some (.wasm WNear.Binary.AllocateUnits.minimumSignature inst WNear.Binary.AllocateUnits.minimumFunction)

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) : Code t inst p := by
  constructor
  · rw [hm];exact h.module
  · exact h.memoryIndex
  · exact h.index568
  · rw [hf];exact h.function568
  · exact h.index569
  · rw [hf];exact h.function569
  · exact h.index572
  · rw [hf];exact h.function572
  · exact h.index573
  · rw [hf];exact h.function573
  · exact h.index574
  · rw [hf];exact h.function574

theorem Native.grown_spec (p : Layout) (hn : Native p) :
    p.grown.wf ∧ p.grown.byteSize=p.memory.byteSize+(delta p).toNat*65536 ∧
    (header p).toNat+12≤p.grown.byteSize ∧ p.record.toNat+8≤p.grown.byteSize := by
  have spec := Memory.grow_spec hn.wf hn.grow
  have old : (oldPages p).toNat=p.memory.size := by
    simp only [oldPages]
    apply Nat.mod_eq_of_lt
    have bound := hn.oldPagesBound
    omega
  have hold : (oldPages p).toNat<65536 := by rw [old];exact hn.oldPagesBound
  have bytes := pageBytes_toNat (oldPages p) hold
  have sz : p.memory.byteSize=p.memory.size*65536 := rfl
  have hdelta := hn.pagesPositive
  have hr := hn.recordBound
  refine ⟨spec.1,spec.2.1,?_,?_⟩
  · change (pageBytes (oldPages p)).toNat+12≤_
    rw [bytes,old,spec.2.1]
    change p.memory.size*65536+12≤p.memory.byteSize+(delta p).toNat*65536
    rw [sz]
    omega
  · rw [spec.2.1]
    change p.record.toNat+8≤p.memory.byteSize+(delta p).toNat*65536
    omega
end WNear.Proofs.AllocateGrowth
