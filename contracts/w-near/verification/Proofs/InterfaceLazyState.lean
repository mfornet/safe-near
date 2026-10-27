import Proofs.InterfaceLazyBody
import Proofs.InterfaceLazySaved
import Proofs.InterfaceLazyFinish

/-! Sequential memories and frame facts for composing the actual lazy body. -/
namespace WNear.Proofs.InterfaceLazyState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  cell : UInt32
  scratch : UInt32
  memory : Memory

def highMemory (p : Layout) := writeI64 p.memory (p.cell.toNat + 4) (readI64 p.memory p.scratch.toNat)
def wordMemory (p : Layout) := writeI32 (highMemory p) (p.cell + 12).toNat (readI32 (highMemory p) (p.scratch + 8).toNat)
def statusMemory (p : Layout) := writeI32 (wordMemory p) p.cell.toNat 1

def oldLow (p : Layout) := readI64 p.memory (p.cell.toNat + 4)
def oldHigh (p : Layout) := readI32 (highMemory p) (p.cell + 12).toNat
def oldStatus (p : Layout) := readI32 (wordMemory p) p.cell.toNat

def highFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 3 (.i64 (oldLow p))}
def wordFrame (frame : CallFrame) (p : Layout) :=
  {frame with locals := ((frame.locals.set! 1 (.i32 (p.cell + 12))).set! 4 (.i32 (oldHigh p)))}
def statusFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 1 (.i32 (oldStatus p))}
def finalFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 0 (.i32 (p.cell + 4))}

def high (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceLazyBody.exchanged64 s op p.memoryIndex p.cell p.scratch p.memory
def word (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceLazyBody.exchanged32 s op p.memoryIndex p.cell p.scratch (highMemory p)
def status (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceLazyBody.replacedStatus s op p.memoryIndex p.cell (wordMemory p)
def saved (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceLazySaved.savedStore s op p.memoryIndex p.scratch (oldStatus p) (oldHigh p) (oldLow p) (statusMemory p)
def finalStore (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceLazyFinish.finalStore s op p.globalIndex p.scratch

/-- Field preservation for a phase; the written memory and charged host are
explicitly excluded. -/
def Resources (before after : Store NearState) : Prop :=
  {after with mems := before.mems, host := before.host} = before

theorem high_resources (s : Store NearState) (op : Nat) (p : Layout) : Resources s (high s op p) := by
  simp only [Resources, high, InterfaceLazyBody.exchanged64, paid, chargedStore, storeI64]
theorem word_resources (s : Store NearState) (op : Nat) (p : Layout) : Resources s (word s op p) := by
  simp only [Resources, word, InterfaceLazyBody.exchanged32, paid, chargedStore, storeI32]
theorem status_resources (s : Store NearState) (op : Nat) (p : Layout) : Resources s (status s op p) := by
  simp only [Resources, status, InterfaceLazyBody.replacedStatus, paid, chargedStore, storeI32]
theorem saved_resources (s : Store NearState) (op : Nat) (p : Layout) : Resources s (saved s op p) := by
  simp only [Resources, saved, InterfaceLazySaved.savedStore, InterfaceLazySaved.savedHigh,
    InterfaceLazySaved.savedLow, InterfaceSetBody.storeWord, paid, chargedStore, storeI32, storeI64]

theorem high_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (7 * op + rest)) : (high s op p).host.gas.Credits rest := by
  simpa only [high, InterfaceLazyBody.exchanged64, storeI64] using paid_credits s op 7 rest hc
theorem word_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (12 * op + rest)) : (word s op p).host.gas.Credits rest := by
  simpa only [word, InterfaceLazyBody.exchanged32, storeI32] using paid_credits s op 12 rest hc
theorem status_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (6 * op + rest)) : (status s op p).host.gas.Credits rest := by
  simpa only [status, InterfaceLazyBody.replacedStatus, storeI32] using paid_credits s op 6 rest hc

theorem high_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) : (high s op p).mems[p.memoryIndex]? = some (highMemory p) := by
  have hp : (paid s op 7).mems[p.memoryIndex]? = some p.memory := by simpa only [paid, chargedStore] using hm
  exact storeI64_memory (paid s op 7) p.memoryIndex (p.cell.toNat + 4) p.memory (readI64 p.memory p.scratch.toNat) hp

theorem word_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some (highMemory p)) : (word s op p).mems[p.memoryIndex]? = some (wordMemory p) := by
  have hp : (paid s op 12).mems[p.memoryIndex]? = some (highMemory p) := by simpa only [paid, chargedStore] using hm
  exact storeI32_memory (paid s op 12) p.memoryIndex (p.cell + 12).toNat (highMemory p) (readI32 (highMemory p) (p.scratch + 8).toNat) hp

theorem status_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some (wordMemory p)) : (status s op p).mems[p.memoryIndex]? = some (statusMemory p) := by
  have hp : (paid s op 6).mems[p.memoryIndex]? = some (wordMemory p) := by simpa only [paid, chargedStore] using hm
  exact storeI32_memory (paid s op 6) p.memoryIndex p.cell.toNat (wordMemory p) 1 hp

theorem saved_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (13 * op + rest)) : (saved s op p).host.gas.Credits rest := by
  have h1 := paid_credits s op 7 (6 * op + rest) (hc.mono (by omega))
  have h2 := paid_credits (paid s op 7) op 3 (3 * op + rest) (h1.mono (by omega))
  have h3 := paid_credits (paid (paid s op 7) op 3) op 3 rest h2
  simpa only [saved, InterfaceLazySaved.savedStore, InterfaceLazySaved.savedHigh,
    InterfaceLazySaved.savedLow, InterfaceSetBody.storeWord, paid, chargedStore, storeI32, storeI64] using h3

theorem Resources.modules (s t : Store NearState) (h : Resources s t) : t.modules = s.modules :=
  congrArg (fun v => v.modules) h

theorem Resources.globals (s t : Store NearState) (h : Resources s t) : t.globals = s.globals :=
  congrArg (fun v => v.globals) h

end WNear.Proofs.InterfaceLazyState
