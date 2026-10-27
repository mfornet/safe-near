import Proofs.AllocateControlFrame
import Proofs.AllocateUnitsMinimum
import Binary.AllocateSearch
import Proofs.AllocatePrefix

/-! Deterministic actual phases and original code resources for the successful
innermost split branch. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Code (s : Store NearState) (p : Layout) (inst : Nat) : Prop where
  module : s.modules[inst]? = some p.mi
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  tableIndex : p.mi.tableAddrs[0]? = some p.tableAddress
  table : s.tables[p.tableAddress]? = some p.table
  callbackElement : p.table.elems[(readI32 p.memory (p.vtable.toNat+16)).toNat]? = some (.func p.callbackAddress)
  callbackType : p.mi.types[13]? = some WNear.Binary.AllocateUnits.quantumSignature
  callbackFunction : s.funcs[p.callbackAddress]? = some (.wasm WNear.Binary.AllocateUnits.quantumSignature p.callbackInst WNear.Binary.AllocateUnits.quantumFunction)
  unitsIndex : p.mi.funcAddrs[572]? = some p.unitsAddress
  unitsFunction : s.funcs[p.unitsAddress]? = some (.wasm WNear.Binary.AllocateUnits.unitsSignature inst WNear.Binary.AllocateUnits.unitsFunction)
  minimumIndex : p.mi.funcAddrs[574]? = some p.minimumAddress
  minimumFunction : s.funcs[p.minimumAddress]? = some (.wasm WNear.Binary.AllocateUnits.minimumSignature inst WNear.Binary.AllocateUnits.minimumFunction)

theorem Code.transport (s t : Store NearState) (p : Layout) (inst : Nat) (h : Code s p inst)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t p inst := by
  exact { h with module:=by rw [hm]; exact h.module
                 table:=by rw [ht]; exact h.table
                 callbackFunction:=by rw [hf]; exact h.callbackFunction
                 unitsFunction:=by rw [hf]; exact h.unitsFunction
                 minimumFunction:=by rw [hf]; exact h.minimumFunction }

theorem Code.charge (s : Store NearState) (cost : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (chargedStore s cost) p inst := h.transport s _ p inst rfl rfl rfl

theorem Code.paid (s : Store NearState) (op count : Nat) (p : Layout) (inst : Nat) (h : Code s p inst) :
    Code (paid s op count) p inst := by
  induction count with
  | zero => exact h
  | succ n ih => exact ih.charge (StorePairCaller.paid s op n) op p inst

def endSubtracted (s : Store NearState) (op : Nat) := paid s op 13
def callbackDone (s : Store NearState) (op : Nat) := Allocate.callbackAfter (endSubtracted s op) op
def arithmeticDone (s : Store NearState) (op : Nat) := paid (callbackDone s op) op 35
def minimumDone (s : Store NearState) (op : Nat) := AllocateUnits.minimumAfter (paid (arithmeticDone s op) op 1) op

def initialized (s : Store NearState) (op : Nat) (p : Layout) :=
  Allocate.initializedStore (minimumDone s op) op p.memoryIndex p.memory (head p) (header p)
def linked (s : Store NearState) (op : Nat) (p : Layout) := controlAfter (initialized s op p) op p
def splitAfter (s : Store NearState) (op : Nat) (p : Layout) :=
  Allocate.committed (linked s op p) op p.memoryIndex (linkedMemory p) (header p)

def splitFrame (frame : CallFrame) (p : Layout) := Allocate.arithmeticFrame
  (Allocate.callbackFrame (Allocate.fitFrame frame p.memory (head p) p.words)) p.memory (head p) p.words
def finalFrame (frame : CallFrame) (p : Layout) := Allocate.resultFrame (controlFrame (splitFrame frame p) p) (header p)

structure FitReady (frame : CallFrame) (p : Layout) : Prop where
  words : frame.locals[0]? = some (.i32 p.words)
  headLocal : frame.locals[1]? = some (.i32 (head p))
  context : frame.locals[3]? = some (.i32 p.context)
  vtable : frame.locals[4]? = some (.i32 p.vtable)
  alignmentMask : frame.locals[6]? = some (.i32 4294967295)
  alignmentFlag : frame.locals[8]? = some (.i32 0)
  dataBase : frame.locals[9]? = some (.i32 (head p+8))
  byteCount : frame.locals[10]? = some (.i32 (p.words*4))
  localSize : 14 ≤ frame.locals.size
end WNear.Proofs.AllocateSearch
