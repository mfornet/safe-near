import Proofs.ValueReturnOuterGlobals

/-! Minimal original resources and exact shared SDK lookup/acquire prefix states. -/
namespace WNear.Proofs.StateDispatchPrefix
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  tableAddress : Nat
  global : GlobalInst
  table : TableInst
  sp : UInt32
  interface : UInt32
  lookupElement : UInt32
  memory : Memory

def scratch (p : Layout) := p.sp - 16

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def lookupBefore (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 2
def looked (s : Store NearState) (op : Nat) (p : Layout) := ValueReturnThreadLocal.indirectAfter (lookupBefore s op p) op

def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (paid (looked s op p) op 3) op 3
def acquired (s : Store NearState) (op : Nat) (p : Layout) :=
  ValueReturnAcquire.calledAcquireStore (arguments s op p) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p) 1074904 p.memory

def reservedFrame (frame : CallFrame) (p : Layout) (slot : Nat) :=
  {frame with locals := frame.locals.set! slot (.i32 (scratch p))}
def guardedFrame (frame : CallFrame) (p : Layout) (slot : Nat) :=
  {reservedFrame frame p slot with locals := (reservedFrame frame p slot).locals.set! 0 (.i32 1074904)}

def prologue (slot : Nat) : List Instr :=
  [.global_get 0,.i32_const 16,.i32_binop .sub,.local_tee slot,.global_set 0]
def lookup : List Instr := [.local_get 0,.load .i32 none {align := 2,offset := 0},.call_indirect 1 0]
def acquire (slot : Nat) (location : UInt32) : List Instr :=
  [.local_tee 0,.i32_eqz,.br_if 0,.local_get slot,.local_get 0,.i32_const location,.call 429]
def inner (slot : Nat) (location : UInt32) (tail : List Instr) := lookup ++ acquire slot location ++ tail
def body (slot : Nat) (location : UInt32) (tail fallback epilogue : List Instr) :=
  prologue slot ++ [.block .empty ([.block .empty (inner slot location tail)] ++ fallback)] ++ epilogue

def nested (frame : CallFrame) (height : Nat) (code fallback epilogue : List Instr) : CallFrame :=
  emptyBlockFrame (emptyBlockFrame frame height (epilogue ++ code)) height fallback

structure Code (s : Store NearState) (p : Layout) (inst : Nat) : Prop where
  module : s.modules[inst]? = some p.mi
  tableIndex : p.mi.tableAddrs[0]? = some p.tableAddress
  table : s.tables[p.tableAddress]? = some p.table
  lookupElement : p.table.elems[p.lookupElement.toNat]? = some (.func 565)
  lookupType : p.mi.types[1]? = some WNear.Binary.ValueReturnThreadLocal.lookupSignature
  lookupFunction : s.funcs[565]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.lookupSignature inst WNear.Binary.ValueReturnThreadLocal.lookupFunction)
  helperIndex : p.mi.funcAddrs[468]? = some 468
  helperFunction : s.funcs[468]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature inst WNear.Binary.ValueReturnThreadLocal.function)
  acquireLinks : ValueReturnAcquire.Links s p.mi inst
  acquireIndex : p.mi.funcAddrs[429]? = some 429
  acquireFunction : s.funcs[429]? = some (.wasm WNear.Binary.ValueReturnAcquire.acquireSignature inst WNear.Binary.ValueReturnAcquire.acquireFunction)
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex

theorem Code.transport (s t : Store NearState) (p : Layout) (inst : Nat)
    (h : Code s p inst) (hf : t.funcs = s.funcs) (hm : t.modules = s.modules)
    (ht : t.tables = s.tables) : Code t p inst := by
  exact {
    module := by rw [hm]; exact h.module
    tableIndex := h.tableIndex
    table := by rw [ht]; exact h.table
    lookupElement := h.lookupElement
    lookupType := h.lookupType
    lookupFunction := by rw [hf]; exact h.lookupFunction
    helperIndex := h.helperIndex
    helperFunction := by rw [hf]; exact h.helperFunction
    acquireLinks := ValueReturnAcquire.links_resources s t p.mi inst hm hf h.acquireLinks
    acquireIndex := h.acquireIndex
    acquireFunction := by rw [hf]; exact h.acquireFunction
    memoryIndex := h.memoryIndex
    globalIndex := h.globalIndex
  }

structure Ready (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (callers : List CallFrame) (p : Layout) (slot : Nat) : Prop where
  code : Code s p frame.inst
  interfaceLocal : frame.locals[0]? = some (.i32 p.interface)
  localSize : slot < frame.locals.size
  slotNe : slot ≠ 0
  memory : s.mems[p.memoryIndex]? = some p.memory
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryWf : p.memory.wf
  interfaceBound : p.interface.toNat + 4 ≤ p.memory.byteSize
  interfaceRead : readI32 p.memory p.interface.toNat = p.lookupElement
  threadBound : 1074900 + 4 ≤ p.memory.byteSize
  threadStatus : readI32 p.memory 1074900 = 1
  cellBound : 1074904 + 4 ≤ p.memory.byteSize
  acquireOutBound : (scratch p).toNat + 8 ≤ p.memory.byteSize
  countAccepted : Numeric.irelop32 .ge_s (ValueReturnAcquire.nextCount p.memory 1074904) 1 = true
  depth : callers.length + 3 < limits.maxCallDepth

theorem paid_globals (s : Store NearState) (op count : Nat) : (paid s op count).globals = s.globals := by
  induction count with
  | zero => rfl
  | succ n ih => exact ih

theorem lookup_globals (s : Store NearState) (op : Nat) :
    (ValueReturnThreadLocal.indirectAfter s op).globals = s.globals := by
  simp only [ValueReturnThreadLocal.indirectAfter,ValueReturnThreadLocal.lookupAfter,
    ValueReturnThreadLocal.callAfter,ValueReturnThreadLocal.entered,ValueReturnThreadLocal.indirectEntered,
    paid_globals,chargedStore]

theorem arguments_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).globals = (reserved s op p).globals := by
  rw [arguments,paid_globals,paid_globals,looked,lookup_globals,lookupBefore,paid_globals]

theorem reserved_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (reserved s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simp only [reserved,setGlobal,paid_globals]
  simp [Array.getElem?_modify,hg]

end WNear.Proofs.StateDispatchPrefix
