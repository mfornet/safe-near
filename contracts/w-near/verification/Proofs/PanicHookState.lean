import Binary.PanicHook
import Proofs.PanicAllocatePointerFrame
import Proofs.PanicHookSetState

/-! Original resources and computed states of the deployed panic-hook setup. -/
namespace WNear.Proofs.PanicHookState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
abbrev Layout := PanicAllocatePointerState.Layout
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

def pointerFrame (inst height : Nat) : CallFrame :=
  {locals := #[.i32 0, .i32 1, .i32 0, .i32 0], inst, arity := 1, height, labels := [], code := []}

/-- Original code/data plus predicates on the explicitly computed heap. There
is no successful invocation, future array lookup, or whole execution premise. -/
structure Ready (s : Store NearState) (limits : ExecLimits) (inst depth : Nat) (p : Layout) : Prop where
  module : s.modules[inst]? = some p.mi
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  function508Index : p.mi.funcAddrs[508]? = some 508
  function508 : s.funcs[508]? = some (.wasm WNear.Binary.PanicAllocate.signature508 inst WNear.Binary.PanicAllocate.function508)
  function509Index : p.mi.funcAddrs[509]? = some 509
  function509 : s.funcs[509]? = some (.wasm WNear.Binary.PanicAllocateZero.signature inst WNear.Binary.PanicAllocateZero.function)
  allocatorIndex : p.mi.funcAddrs[503]? = some 503
  allocator : s.funcs[503]? = some (.wasm WNear.Binary.PanicAllocate.signature503 inst WNear.Binary.PanicAllocate.function503)
  hookIndex : p.mi.funcAddrs[822]? = some 822
  hook : s.funcs[822]? = some (.wasm WNear.Binary.PanicHookSet.signature inst WNear.Binary.PanicHookSet.function)
  wf : p.memory.wf
  width : p.memory.byteSize ≤ 2 ^ 32
  spLower : 32 ≤ p.sp.toNat
  stackBound : p.sp.toNat ≤ p.memory.byteSize
  depth : depth + 2 < limits.maxCallDepth
  hookSpan : 1074936 ≤ (PanicAllocatePointerState.finalMemory p).byteSize
  initial : readI32 (PanicAllocatePointerState.finalMemory p) 1074932 = 0
  unlocked : readI32 (PanicAllocatePointerState.finalMemory p) 1074920 = 0
  oldVtable : readI32 (PanicAllocatePointerState.finalMemory p) 1074928 = 0

theorem Ready.charge (s : Store NearState) (cost : Nat) (limits : ExecLimits) (inst depth : Nat) (p : Layout)
    (hr : Ready s limits inst depth p) : Ready (chargedStore s cost) limits inst depth p := by
  rcases hr with ⟨hm, hgi, hg, hsp, hmi, hmem, h508i, h508, h509i, h509, hai, ha, hhi, hh,
    hwf, hwidth, hlow, hbound, hd, hs, hinit, hunlock, hold⟩
  exact ⟨hm, hgi, hg, hsp, hmi, hmem, h508i, h508, h509i, h509, hai, ha, hhi, hh,
    hwf, hwidth, hlow, hbound, hd, hs, hinit, hunlock, hold⟩

theorem Ready.paid (s : Store NearState) (op n : Nat) (limits : ExecLimits) (inst depth : Nat) (p : Layout)
    (hr : Ready s limits inst depth p) : Ready (StorePairCaller.paid s op n) limits inst depth p := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ih.charge _ op limits inst depth p

theorem Ready.pointer_ready (s : Store NearState) (limits : ExecLimits) (inst depth : Nat) (p : Layout)
    (hr : Ready s limits inst depth p) (height : Nat) (callers : List CallFrame) (hd : callers.length ≤ depth) :
    PanicAllocatePointerState.Ready s limits (pointerFrame inst height) callers p := by
  exact ⟨hr.module, hr.globalIndex, hr.global, hr.sp, hr.memoryIndex, hr.memory, hr.function508Index, hr.function508,
    hr.function509Index, hr.function509, rfl, rfl, by simp [pointerFrame], hr.wf, hr.width, hr.spLower, hr.stackBound,
    by have bound := hr.depth; omega⟩

def allocationEntry (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def allocated (s : Store NearState) (op : Nat) (p : Layout) :=
  PanicAllocatePointerState.after (allocationEntry (paid s op 2) op) op p

def hookArguments (s : Store NearState) (op : Nat) (p : Layout) := paid (allocated s op p) op 1
def hookEntry (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def after (s : Store NearState) (op : Nat) (p : Layout) :=
  PanicHookSet.after (hookEntry (hookArguments s op p) op) op p.memoryIndex (PanicAllocatePointerState.finalMemory p) 1 1055136

def finalMemory (p : Layout) := PanicHookSet.finalMemory (PanicAllocatePointerState.finalMemory p) 1 1055136

theorem allocated_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (88 * op + rest)) : (allocated s op p).host.gas.Credits rest := by
  have c2 := paid_credits s op 2 (86 * op + rest) (hc.mono (by omega))
  have hop := StorePair.charged_credits (paid s op 2) op (10 * op + (75 * op + rest)) (c2.mono (by omega))
  have ca := StorePair.charged_credits (chargedStore (paid s op 2) op) (10 * op) (75 * op + rest) hop
  exact PanicAllocatePointerState.after_credits (allocationEntry (paid s op 2) op) op rest p ca

theorem allocated_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) : (allocated s op p).mems[p.memoryIndex]? = some (PanicAllocatePointerState.finalMemory p) := by
  have initial : (allocationEntry (paid s op 2) op).mems[p.memoryIndex]? = some p.memory := by
    simpa only [allocationEntry, paid, chargedStore] using hm
  exact PanicAllocatePointerState.after_memory (allocationEntry (paid s op 2) op) op p initial

theorem allocated_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (allocated s op p).funcs = s.funcs ∧ (allocated s op p).modules = s.modules ∧ (allocated s op p).tables = s.tables := by
  have result := PanicAllocatePointerState.after_fields (allocationEntry (paid s op 2) op) op p
  simpa only [allocated, allocationEntry, paid, chargedStore] using result

theorem allocated_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (allocated s op p).globals = s.globals := by
  have initial : (allocationEntry (paid s op 2) op).globals[p.globalIndex]? = some p.global := by
    simpa only [allocationEntry, paid, chargedStore] using hg
  have result := PanicAllocatePointerState.after_globals (allocationEntry (paid s op 2) op) op p initial hsp
  simpa only [allocated, allocationEntry, paid, chargedStore] using result

theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (131 * op + rest)) : (after s op p).host.gas.Credits rest := by
  have alloc := allocated_credits s op (43 * op + rest) p (hc.mono (by omega))
  have arg := paid_credits (allocated s op p) op 1 (42 * op + rest) (alloc.mono (by omega))
  have hop := StorePair.charged_credits (hookArguments s op p) op (10 * op + (31 * op + rest)) (arg.mono (by omega))
  have ca := StorePair.charged_credits (chargedStore (hookArguments s op p) op) (10 * op) (31 * op + rest) hop
  exact PanicHookSet.after_credits (hookEntry (hookArguments s op p) op) op p.memoryIndex rest (PanicAllocatePointerState.finalMemory p) 1 1055136 ca

end WNear.Proofs.PanicHookState
