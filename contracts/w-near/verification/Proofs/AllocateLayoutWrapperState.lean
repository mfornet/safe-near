import Proofs.AllocateLayoutWrapperSteps

/-! Original resources and exact sequential states of f752/f685. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  sp : UInt32
  out : UInt32
  size : UInt32
  memory : Memory
  calleeIndex : Nat
  calleeAddress : Nat
  message : UInt32
  location : UInt32
  previous : UInt32

def scratch (p : Layout) := p.sp - 16
def alignmentMemory (p : Layout) := writeI32 p.memory ((scratch p).toNat + 12) 1
def setupMemory (p : Layout) := writeI32 (alignmentMemory p) ((scratch p).toNat + 8) p.size
def reserved (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def alignmentStore (s : Store NearState) (op : Nat) (p : Layout) := constantStore (reserved s op p) op p.memoryIndex 12 (scratch p) 1 p.memory
def setupStore (s : Store NearState) (op : Nat) (p : Layout) := InterfaceSetBody.storeWord (alignmentStore s op p) op p.memoryIndex 8 (scratch p) p.size (alignmentMemory p)
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (setupStore s op p) op 4

def leafLayout (p : Layout) : AllocateLayout.Layout :=
  {mi := p.mi,globalIndex := p.globalIndex,memoryIndex := p.memoryIndex,
   global := {p.global with value := .i32 (scratch p)},sp := scratch p,out := scratch p,input := scratch p + 8,memory := setupMemory p}
def laidOut (s : Store NearState) (op : Nat) (p : Layout) := AllocateLayout.called (arguments s op p) op (leafLayout p)
def laidOutMemory (p : Layout) := AllocateLayout.finalMemory (leafLayout p)
def copied (s : Store NearState) (op : Nat) (p : Layout) := copyStore (laidOut s op p) op p.memoryIndex p.out (scratch p) (laidOutMemory p)
-- Final memory is named directly, without materializing any concrete page array.
def finalMemory (p : Layout) := (laidOutMemory p).writeRun p.out.toNat 8 fun i => UInt8.ofNat ((readI64 (laidOutMemory p) (scratch p).toNat).toNat >>> (8 * i))
def after (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid (copied s op p) op 4) p.globalIndex (.i32 (scratch p + 16))
def afterFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 2 (.i32 (scratch p))}

structure Ready (s : Store NearState) (frame : CallFrame) (p : Layout) : Prop where
  module : s.modules[frame.inst]? = some p.mi
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  functionIndex : p.mi.funcAddrs[p.calleeIndex]? = some p.calleeAddress
  function : s.funcs[p.calleeAddress]? = some (.wasm WNear.Binary.AllocateLayout.signature frame.inst
    (WNear.Binary.AllocateLayout.function p.message p.location p.previous))
  out : frame.locals[0]? = some (.i32 p.out)
  size : frame.locals[1]? = some (.i32 p.size)
  locals : 3 ≤ frame.locals.size
  wf : p.memory.wf
  width : p.memory.byteSize ≤ 2 ^ 32
  scratchBound : (scratch p).toNat + 16 ≤ p.memory.byteSize
  outBound : p.out.toNat + 8 ≤ p.memory.byteSize

/-- The initial stack span derives the actual inner input's native address,
not a future memory observation or alignment assertion. -/
theorem setup_spec (p : Layout) (hw : p.memory.wf) (hb : (scratch p).toNat + 16 ≤ p.memory.byteSize) :
    (setupMemory p).wf ∧ (setupMemory p).byteSize = p.memory.byteSize ∧ (setupMemory p).max = p.memory.max ∧
    readI32 (setupMemory p) ((scratch p).toNat + 8) = p.size ∧ readI32 (setupMemory p) ((scratch p).toNat + 12) = 1 := by
  have a := writeI32_spec p.memory ((scratch p).toNat + 12) 1 hw (by omega)
  have sb : (scratch p).toNat + 8 + 4 ≤ (alignmentMemory p).byteSize := by rw [show (alignmentMemory p).byteSize = p.memory.byteSize from a.2.1]; omega
  have b := writeI32_spec (alignmentMemory p) ((scratch p).toNat + 8) p.size a.1 sb
  have low := PanicAllocateReadback.read_write_self (alignmentMemory p) ((scratch p).toNat + 8) p.size a.1 sb
  have high := PanicAllocateReadback.read_write_frame (alignmentMemory p) ((scratch p).toNat + 12) ((scratch p).toNat + 8) p.size a.1 sb (by omega)
  have high0 := PanicAllocateReadback.read_write_self p.memory ((scratch p).toNat + 12) 1 hw (by omega)
  exact ⟨b.1,b.2.1.trans a.2.1,b.2.2.1.trans a.2.2.1,low,high.trans high0⟩

end WNear.Proofs.AllocateLayoutWrapper
