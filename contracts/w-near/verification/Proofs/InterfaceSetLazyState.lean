import Proofs.InterfaceSetSetup
import Proofs.InterfaceSetReady
import Proofs.InterfaceSetFrame
import Proofs.ValueReturnLazyLookup
import Proofs.InterfaceLazyLayout

/-! Original structural resources for the setter's actual lazy lookup. -/
namespace WNear.Proofs.InterfaceSetLazyState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
open WNear.Proofs.InterfaceSetState
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

def lookupLayout (p : Layout) (initializerAddress : Nat) : InterfaceLazyComplete.Layout :=
  {mi := p.mi
   globalIndex := p.globalIndex
   memoryIndex := p.memoryIndex
   global := {p.global with value := .i32 (scratch p)}
   tableAddress := p.tableAddress
   initializerAddress
   table := p.table
   sp := scratch p
   cell := 1074900
   location := 106
   memory := savedMemory p}

def memory (p : Layout) (initializerAddress : Nat) := InterfaceLazyLayout.finalMemory (lookupLayout p initializerAddress)
def looked (s : Store NearState) (op : Nat) (p : Layout) (initializerAddress : Nat) :=
  ValueReturnLazyLookup.indirectAfter (lookupBefore s op p) op (lookupLayout p initializerAddress)

/-- Original code, words and native bounds. In particular the initializer is
linked through the actual table and the preexisting thread-local status is read. -/
structure Setup (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (initializerAddress : Nat) : Prop where
  code : Code s p frame.inst
  interfaceLocal : frame.locals[0]? = some (.i32 p.interface)
  receiverLocal : frame.locals[1]? = some (.i32 p.receiver)
  vtableLocal : frame.locals[2]? = some (.i32 p.vtable)
  localSize : 4 ≤ frame.locals.size
  memory : s.mems[p.memoryIndex]? = some p.memory
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  firstBound : (scratch p).toNat + 20 + 4 ≤ p.memory.byteSize
  secondBound : (scratch p).toNat + 16 + 4 ≤ (writeI32 p.memory ((scratch p).toNat + 20) p.vtable).byteSize
  interfaceBound : p.interface.toNat + 4 ≤ (savedMemory p).byteSize
  interfaceRead : readI32 (savedMemory p) p.interface.toNat = p.lookupElement
  statusBound : 1074900 + 4 ≤ (savedMemory p).byteSize
  status : readI32 (savedMemory p) 1074900 ≠ 1
  lazyIndex : p.mi.funcAddrs[467]? = some 467
  lazyFunction : s.funcs[467]? = some (.wasm WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function)
  initializerElement : p.table.elems[106]? = some (.func initializerAddress)
  initializerType : p.mi.types[0]? = some WNear.Binary.InterfaceInitialize.signature
  initializerFunction : s.funcs[initializerAddress]? = some (.wasm WNear.Binary.InterfaceInitialize.signature frame.inst WNear.Binary.InterfaceInitialize.function)
  initializerBound : (InterfaceLazyComplete.scratch (lookupLayout p initializerAddress)).toNat + 8 ≤ (savedMemory p).byteSize
  tail : InterfaceLazyTail.Bounds (InterfaceLazyComplete.tailLayout (lookupLayout p initializerAddress))
  depth : callers.length + 4 < limits.maxCallDepth

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs = s.funcs := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem lookupBefore_funcs (s : Store NearState) (op : Nat) (p : Layout) :
    (lookupBefore s op p).funcs = s.funcs := by
  simp only [lookupBefore, savedArguments, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord,
    reserved, paid_funcs, storeI32_funcs, setGlobal]

theorem lookupBefore_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (lookupBefore s op p).mems[p.memoryIndex]? = some (savedMemory p) := by
  rw [lookupBefore, paid_mems]
  exact InterfaceSetPhases.savedArguments_memory s op p hm

theorem lookupBefore_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (lookupBefore s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simp only [lookupBefore, savedArguments, InterfaceSetBody.twoWordsStore, InterfaceSetBody.storeWord,
    storeI32_globals, paid_globals, reserved, setGlobal]
  simp [Array.getElem?_modify, hg]

theorem resources (s : Store NearState) (op : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (initializerAddress : Nat)
    (hr : Setup s limits frame callers p initializerAddress) :
    ValueReturnLazyLookup.Resources (lookupBefore s op p) limits frame.inst (callers.length + 3)
      (lookupLayout p initializerAddress) := by
  have c := InterfaceSetPhases.lookupBefore_code s op p frame.inst hr.code
  have hf : (lookupBefore s op p).funcs[initializerAddress]? = some
      (.wasm WNear.Binary.InterfaceInitialize.signature frame.inst WNear.Binary.InterfaceInitialize.function) := by
    rw [lookupBefore_funcs]; exact hr.initializerFunction
  exact ⟨c.module, c.globalIndex, lookupBefore_global s op p hr.global, rfl, c.memoryIndex,
    lookupBefore_memory s op p hr.memory, c.tableIndex, c.table, hr.initializerElement, hr.initializerType,
    hf, hr.initializerBound, by have h := hr.depth; omega, hr.tail⟩

end WNear.Proofs.InterfaceSetLazyState
