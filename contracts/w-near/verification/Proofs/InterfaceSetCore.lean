import Proofs.InterfaceSetTail
import Proofs.InterfaceBorrowAcquire
import Proofs.InterfaceSetFrame
import Proofs.InterfaceSetReady

/-! The real setter suffix after lookup, parameterized by the actual current
heap. No initial argument-saving writes are baked into this memory snapshot. -/
namespace WNear.Proofs.InterfaceSetCore
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open InterfaceSetState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

def arguments (s : Store NearState) (op : Nat) := paid (paid s op 3) op 5

def acquired (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory) :=
  InterfaceBorrow.calledAcquireStore (arguments s op) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p + 8) 1074904 memory

def acquiredMemory (p : Layout) (memory : Memory) :=
  InterfaceBorrow.recordMemory (writeI32 memory 1074904 4294967295) (scratch p + 8) 1074904

def highMemory (p : Layout) (memory : Memory) := writeI32 (acquiredMemory p memory) ((scratch p).toNat + 28)
  (readI32 (acquiredMemory p memory) ((scratch p).toNat + 12))
def pointer (p : Layout) (memory : Memory) := readI32 (highMemory p memory) ((scratch p).toNat + 8)
def lowMemory (p : Layout) (memory : Memory) := writeI32 (highMemory p memory) ((scratch p).toNat + 24) (pointer p memory)
def installedMemory (p : Layout) (memory : Memory) :=
  InterfaceInstall.installMemory (lowMemory p memory) (pointer p memory).toNat p.receiver p.vtable

def counter (p : Layout) (memory : Memory) := readI32 (installedMemory p memory) (((scratch p + 24) ||| 4).toNat)
def installed (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory) :=
  InterfaceSetTail.installed (acquired s op p memory) op p (acquiredMemory p memory) (highMemory p memory) (lowMemory p memory)
def after (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory) :=
  InterfaceSetTail.after (acquired s op p memory) op p (counter p memory)
    (acquiredMemory p memory) (highMemory p memory) (lowMemory p memory) (installedMemory p memory)

def guardedFrame (frame : CallFrame) := {frame with locals := frame.locals.set! 0 (.i32 1074904)}
def finalFrame (frame : CallFrame) (p : Layout) (memory : Memory) :=
  InterfaceSetTail.finalFrame (guardedFrame frame) p (highMemory p memory)

/-- Only current resource/data predicates. The memory argument is the actual
post-lookup heap and is independent of p.memory and Phases.savedMemory. -/
structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (memory : Memory) : Prop where
  code : Code s p frame.inst
  scratchLocal : frame.locals[3]? = some (.i32 (scratch p))
  receiverLocal : frame.locals[1]? = some (.i32 p.receiver)
  vtableLocal : frame.locals[2]? = some (.i32 p.vtable)
  localSize : 4 ≤ frame.locals.size
  memoryLookup : s.mems[p.memoryIndex]? = some memory
  global : s.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)}
  memoryWf : memory.wf
  cellBound : 1074904 + 4 ≤ memory.byteSize
  cellEmpty : readI32 memory 1074904 = 0
  outBound : (scratch p + 8).toNat + 8 ≤ memory.byteSize
  highReadBound : (scratch p).toNat + 12 + 4 ≤ (acquiredMemory p memory).byteSize
  highWriteBound : (scratch p).toNat + 28 + 4 ≤ (acquiredMemory p memory).byteSize
  lowReadBound : (scratch p).toNat + 8 + 4 ≤ (highMemory p memory).byteSize
  lowWriteBound : (scratch p).toNat + 24 + 4 ≤ (highMemory p memory).byteSize
  lowMemoryWf : (lowMemory p memory).wf
  pointerBound : (pointer p memory).toNat + 8 ≤ (lowMemory p memory).byteSize
  existingEmpty : readI32 (lowMemory p memory) (pointer p memory).toNat = 0
  recordBound : ((scratch p + 24) ||| 4).toNat + 4 ≤ (installedMemory p memory).byteSize
  counterBound : (counter p memory).toNat + 4 ≤ (installedMemory p memory).byteSize
  depth : callers.length + 3 < limits.maxCallDepth

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_code (s : Store NearState) (op n : Nat) (p : Layout) (inst : Nat)
    (h : Code s p inst) : Code (paid s op n) p inst := by
  have hr := StorePairCaller.paid_resources s op n
  have hf := congrArg (fun t : Store NearState => t.funcs) hr
  have hm := congrArg (fun t : Store NearState => t.modules) hr
  have ht := congrArg (fun t : Store NearState => t.tables) hr
  exact h.transport s _ p inst hf hm ht

private theorem arguments_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat)
    (h : Code s p inst) : Code (arguments s op) p inst :=
  paid_code _ op 5 p inst (paid_code s op 3 p inst h)

private theorem arguments_memory (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (h : s.mems[p.memoryIndex]? = some memory) : (arguments s op).mems[p.memoryIndex]? = some memory := by
  rw [arguments, paid_mems, paid_mems]; exact h
private theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout)
    (h : s.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)}) :
    (arguments s op).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  rw [arguments, paid_globals, paid_globals]; exact h

private theorem acquired_memory (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hm : s.mems[p.memoryIndex]? = some memory) :
    (acquired s op p memory).mems[p.memoryIndex]? = some (acquiredMemory p memory) := by
  have h := InterfaceBorrow.calledAcquireStore_memory (arguments s op) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p + 8) 1074904 memory (arguments_memory s op p memory hm)
  have hn : (1074904 : UInt32).toNat = (1074904 : Nat) := rfl
  simpa only [acquired, acquiredMemory, hn] using h

private theorem high_memory (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hm : s.mems[p.memoryIndex]? = some memory) :
    (InterfaceSetInstallTail.highStore (acquired s op p memory) op p.memoryIndex (scratch p) (acquiredMemory p memory)).mems[p.memoryIndex]? =
      some (highMemory p memory) := by
  have hp : (paid (acquired s op p memory) op 4).mems[p.memoryIndex]? = some (acquiredMemory p memory) := by
    rw [paid_mems]; exact acquired_memory s op p memory hm
  have h := storeI32_memory (paid (acquired s op p memory) op 4) p.memoryIndex ((scratch p).toNat + 28)
    (acquiredMemory p memory) (readI32 (acquiredMemory p memory) ((scratch p).toNat + 12)) hp
  simpa only [InterfaceSetInstallTail.highStore, InterfaceSetBody.copiedWord, highMemory] using h

private theorem low_memory (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hm : s.mems[p.memoryIndex]? = some memory) :
    (InterfaceSetInstallTail.lowStore (acquired s op p memory) op p.memoryIndex (scratch p) (acquiredMemory p memory) (highMemory p memory)).mems[p.memoryIndex]? =
      some (lowMemory p memory) := by
  let high := InterfaceSetInstallTail.highStore (acquired s op p memory) op p.memoryIndex (scratch p) (acquiredMemory p memory)
  have hp : (paid high op 5).mems[p.memoryIndex]? = some (highMemory p memory) := by
    rw [paid_mems]; exact high_memory s op p memory hm
  have h := storeI32_memory (paid high op 5) p.memoryIndex ((scratch p).toNat + 24)
    (highMemory p memory) (readI32 (highMemory p memory) ((scratch p).toNat + 8)) hp
  simpa only [InterfaceSetInstallTail.lowStore, InterfaceSetBody.copiedTeeWord, high, lowMemory, pointer] using h

private theorem installed_memory (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hm : s.mems[p.memoryIndex]? = some memory) :
    (installed s op p memory).mems[p.memoryIndex]? = some (installedMemory p memory) := by
  let before := InterfaceSetInstallTail.guardedStore (acquired s op p memory) op p.memoryIndex (scratch p) (acquiredMemory p memory) (highMemory p memory)
  have hp : before.mems[p.memoryIndex]? = some (lowMemory p memory) := by
    simpa only [before, InterfaceSetInstallTail.guardedStore, InterfaceInstall.guardAfter,
      InterfaceInstall.guardEntry, paid_mems, chargedStore] using low_memory s op p memory hm
  have h := InterfaceSetPhases.twoWordsStore_memory before op p.memoryIndex 4 0 (pointer p memory) p.vtable p.receiver (lowMemory p memory) hp
  simpa only [installed, InterfaceSetTail.installed, InterfaceSetInstallTail.after, installedMemory, InterfaceInstall.installMemory,
    before, pointer, Nat.add_zero] using h

private theorem acquired_global (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hg : s.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)}) :
    (acquired s op p memory).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have ha := arguments_global s op p hg
  have he := InterfaceSetPhases.calledAcquireStore_globals (arguments s op) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p + 8) 1074904 memory {p.global with value := .i32 (scratch p)} ha rfl
  rw [acquired, he]; exact ha

private theorem installed_global (s : Store NearState) (op : Nat) (p : Layout) (memory : Memory)
    (hg : s.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)}) :
    (installed s op p memory).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  rw [installed, InterfaceSetTail.installed, InterfaceSetPhases.installTail_globals]
  exact acquired_global s op p memory hg

/-- Actual setter instructions following the lookup, for an arbitrary current
heap. The guard, f441/f492/f672, installation, f442 and f433 all execute here. -/
theorem wp_core (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (memory : Memory) (post : Post)
    (hr : Ready s limits frame callers p memory)
    (hc : s.host.gas.Credits (180 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p memory) limits base.toArray
      (finalFrame frame p memory) callers code)) rest post) :
    WP cfg (fuel + 125) (.next (atCode s limits (base.toArray.push (.i32 1074904))
      (nested frame base.toArray.size code) callers
      (WNear.Binary.InterfaceSet.acquire ++ WNear.Binary.InterfaceSet.copyBorrow ++
        WNear.Binary.InterfaceSet.guard ++ WNear.Binary.InterfaceSet.install ++ WNear.Binary.InterfaceSet.release)))
      (180 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let gf := guardedFrame frame
  let nf := nested frame base.toArray.size code
  let ng := nested gf base.toArray.size code
  let tail := WNear.Binary.InterfaceSet.copyBorrow ++ WNear.Binary.InterfaceSet.guard ++
    WNear.Binary.InterfaceSet.install ++ WNear.Binary.InterfaceSet.release
  have cg : (paid s op 3).host.gas.Credits (177 * op + rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  have ca : (arguments s op).host.gas.Credits (71 * op + (101 * op + rest)) :=
    paid_credits (paid s op 3) op 5 _ (cg.mono (by omega))
  have cw : (acquired s op p memory).host.gas.Credits (101 * op + rest) :=
    (InterfaceBorrow.calledAcquireStore_gas (arguments s op) op p.globalIndex p.memoryIndex (101 * op + rest)
      (scratch p) (scratch p + 8) 1074904 memory ca).2.2
  have cargs := arguments_code s op p frame.inst hr.code
  have cAcq : Code (acquired s op p memory) p gf.inst := by
    have h := InterfaceSetPhases.acquire_code (arguments s op) op p.globalIndex p.memoryIndex
      (scratch p) (scratch p + 8) 1074904 memory p frame.inst cargs
    simpa only [acquired, gf, guardedFrame] using h
  have cInst : Code (installed s op p memory) p gf.inst := by
    have h := InterfaceSetPhases.install_code (acquired s op p memory) op p.memoryIndex (scratch p)
      p.receiver p.vtable (acquiredMemory p memory) (highMemory p memory) (lowMemory p memory) p gf.inst cAcq
    simpa only [installed, InterfaceSetTail.installed] using h
  have hsG : gf.locals[3]? = some (.i32 (scratch p)) := by simpa [gf, guardedFrame] using hr.scratchLocal
  have hrG : gf.locals[1]? = some (.i32 p.receiver) := by simpa [gf, guardedFrame] using hr.receiverLocal
  have hvG : gf.locals[2]? = some (.i32 p.vtable) := by simpa [gf, guardedFrame] using hr.vtableLocal
  have hnG : 4 ≤ gf.locals.size := by simpa only [gf, guardedFrame, Array.size_set!] using hr.localSize
  have nextTail : WP cfg fuel (.next (atCode
      (InterfaceSetTail.after (acquired s op p memory) op p (counter p memory)
        (acquiredMemory p memory) (highMemory p memory) (lowMemory p memory) (installedMemory p memory))
      limits base.toArray (InterfaceSetTail.finalFrame gf p (highMemory p memory)) callers code)) rest post := by
    simpa only [after, finalFrame, gf, op] using hnext
  have tailProof := InterfaceSetTail.wp_tail cfg fuel rest (acquired s op p memory) limits base gf callers code p
    (counter p memory) (acquiredMemory p memory) (highMemory p memory) (lowMemory p memory) (installedMemory p memory)
    {p.global with value := .i32 (scratch p)} post hsG hrG hvG hnG cAcq
    (acquired_memory s op p memory hr.memoryLookup) (high_memory s op p memory hr.memoryLookup)
    (low_memory s op p memory hr.memoryLookup) hr.highReadBound hr.highWriteBound hr.lowReadBound hr.lowWriteBound
    hr.lowMemoryWf hr.pointerBound hr.existingEmpty cInst (installed_global s op p memory hr.global) rfl
    (installed_memory s op p memory hr.memoryLookup) rfl hr.recordBound hr.counterBound
    (by have h := hr.depth; omega) cw nextTail
  have cA : Code (arguments s op) p ng.inst := by simpa only [ng, gf, nested, guardedFrame, emptyBlockFrame] using cargs
  have links : InterfaceBorrow.Links (arguments s op) p.mi ng.inst :=
    ⟨cA.module, ⟨672, cA.swapIndex, cA.swapFunction⟩, ⟨492, cA.takeIndex, cA.takeFunction⟩⟩
  have hmA := arguments_memory s op p memory hr.memoryLookup
  have hgA := arguments_global s op p hr.global
  have hcell : (1074904 : UInt32).toNat = (1074904 : Nat) := rfl
  have callRule := InterfaceBorrow.wp_call_acquire cfg (fuel + 70) (101 * op + rest) (arguments s op) limits base ng callers tail
    (scratch p) (scratch p + 8) 1074904 1055120 p.mi 441 p.globalIndex p.memoryIndex
    {p.global with value := .i32 (scratch p)} memory post links cA.acquireIndex cA.acquireFunction cA.globalIndex hgA rfl
    cA.memoryIndex hmA hr.memoryWf (by simpa only [hcell] using hr.cellBound) hr.outBound
    (by simpa only [hcell] using hr.cellEmpty) (by decide) hr.depth ca
  have callNext : WP cfg (fuel + 70) (.next (atCode
      (InterfaceBorrow.calledAcquireStore (arguments s op) op p.globalIndex p.memoryIndex (scratch p) (scratch p + 8) 1074904 memory)
      limits base.toArray ng callers tail)) (101 * op + rest) post := by
    simpa only [acquired, ng, tail, op] using tailProof
  have called := callRule callNext
  have hscratch : ng.locals[3]? = some (.i32 (scratch p)) := hsG
  have hptr : ng.locals[0]? = some (.i32 1074904) := by
    simp [ng, gf, nested, guardedFrame, emptyBlockFrame, show 0 < frame.locals.size by have h := hr.localSize; omega]
  have hargs : (base ++ [Value.i32 (scratch p + 8), .i32 1074904, .i32 1055120]).toArray =
      (((base.toArray.push (.i32 (scratch p + 8))).push (.i32 1074904)).push (.i32 1055120)) := by
    apply Array.toList_inj.mp; simp
  have argsNext : WP cfg ((fuel + 70) + 47) (.next (atCode (paid (paid s op 3) op 5) limits
      (((base.toArray.push (.i32 (scratch p + 8))).push (.i32 1074904)).push (.i32 1055120)) ng callers
      (.call 441 :: tail))) (71 * op + (101 * op + rest)) post := by
    simpa only [arguments, op, hargs] using called
  have argsRule := InterfaceSetBody.wp_acquire_arguments cfg ((fuel + 70) + 47) (71 * op + (101 * op + rest))
    (paid s op 3) limits base.toArray ng callers (.call 441 :: tail) (scratch p) 1074904 post
    hscratch hptr (cg.mono (by dsimp [op]; omega))
  have arged := argsRule argsNext
  let argsCode := [.local_get 3, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 1055120, .call 441] ++ tail
  have guardNext : WP cfg (((fuel + 70) + 47) + 5) (.next (atCode (paid s op 3) limits base.toArray
      {nf with locals := nf.locals.set! 0 (.i32 1074904)} callers argsCode)) (5 * op + (71 * op + (101 * op + rest))) post := by
    simpa only [ng, nf, gf, nested, guardedFrame, emptyBlockFrame, argsCode, op, List.cons_append, List.nil_append] using arged
  have guardRule := ValueReturnOuter.wp_cell_guard cfg (((fuel + 70) + 47) + 5) (5 * op + (71 * op + (101 * op + rest)))
    s limits base.toArray nf callers argsCode 1074904 post (by decide) (hc.mono (by dsimp [op]; omega))
  have result := guardRule guardNext
  have fe : fuel + 70 + 47 + 5 + 3 = fuel + 125 := by omega
  have ge : 3 * cfg.regularOpCost + (5 * op + (71 * op + (101 * op + rest))) = 180 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have ce : [.local_tee 0, .i32_eqz, .br_if 0] ++ argsCode =
      WNear.Binary.InterfaceSet.acquire ++ WNear.Binary.InterfaceSet.copyBorrow ++ WNear.Binary.InterfaceSet.guard ++
        WNear.Binary.InterfaceSet.install ++ WNear.Binary.InterfaceSet.release := by
    simp only [WNear.Binary.InterfaceSet.acquire, argsCode, tail, List.cons_append, List.nil_append]
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits _ nf callers _ _ post fe ge ce result

/-- Original credit covers the scalar guard/arguments and actual borrow entry. -/
theorem acquired_credits (s : Store NearState) (op rest : Nat) (p : Layout) (memory : Memory)
    (hc : s.host.gas.Credits (79 * op + rest)) : (acquired s op p memory).host.gas.Credits rest := by
  have cg := paid_credits s op 3 (76 * op + rest) (hc.mono (by omega))
  have ca := paid_credits (paid s op 3) op 5 (71 * op + rest) (cg.mono (by omega))
  exact (InterfaceBorrow.calledAcquireStore_gas (arguments s op) op p.globalIndex p.memoryIndex rest
    (scratch p) (scratch p + 8) 1074904 memory ca).2.2

/-- Residual credit of the exact final state, from the original180-unit budget. -/
theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout) (memory : Memory)
    (hc : s.host.gas.Credits (180 * op + rest)) : (after s op p memory).host.gas.Credits rest := by
  have ca := acquired_credits s op (101 * op + rest) p memory (hc.mono (by omega))
  have ci := InterfaceSetTail.installed_credits (acquired s op p memory) op (71 * op + rest) p
    (acquiredMemory p memory) (highMemory p memory) (lowMemory p memory) (ca.mono (by omega))
  have carg := paid_credits (installed s op p memory) op 5 (36 * op + (30 * op + rest)) (ci.mono (by omega))
  have cr := InterfaceBorrow.calledReleaseStore_credits (paid (installed s op p memory) op 5) op p.memoryIndex
    (30 * op + rest) (counter p memory) (installedMemory p memory) carg
  let rel := InterfaceBorrow.calledReleaseStore (paid (installed s op p memory) op 5) op p.memoryIndex (counter p memory) (installedMemory p memory)
  have cs := paid_credits rel op 2 (28 * op + rest) (cr.mono (by omega))
  have cb := StorePair.charged_credits (paid rel op 2) op (27 * op + rest) (cs.mono (by omega))
  have cget := paid_credits (chargedStore (paid rel op 2) op) op 1 (22 * op + (4 * op + rest)) (cb.mono (by omega))
  have cc := ValueReturnOuter.checkAfter_credits (paid (chargedStore (paid rel op 2) op) op 1) op p.globalIndex
    (4 * op + rest) (scratch p) cget
  have cf := paid_credits (ValueReturnOuter.checkAfter (paid (chargedStore (paid rel op 2) op) op 1) op p.globalIndex (scratch p)) op 4 rest cc
  simpa only [after, installed, InterfaceSetTail.after, InterfaceSetReleaseTail.after,
    InterfaceSetReleaseTail.epilogueAfter, InterfaceSetReleaseTail.released, rel, setGlobal] using cf

end WNear.Proofs.InterfaceSetCore
