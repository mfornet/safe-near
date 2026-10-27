import Proofs.InterfaceLazyTail
import Proofs.InterfaceLazyPrefix

/-! Complete actual f467 body on its old-status-zero path. -/
namespace WNear.Proofs.InterfaceLazyComplete
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  tableAddress : Nat
  initializerAddress : Nat
  table : TableInst
  sp : UInt32
  cell : UInt32
  location : UInt32
  memory : Memory

def scratch (p : Layout) := p.sp - 48

def tailLayout (p : Layout) : InterfaceLazyState.Layout :=
  {mi := p.mi, globalIndex := p.globalIndex, memoryIndex := p.memoryIndex,
   global := {p.global with value := .i32 (scratch p)}, cell := p.cell, scratch := scratch p,
   memory := writeI64 p.memory (scratch p).toNat 0}

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def initialized (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceLazyPrefix.after (reserved s op p) op p.memoryIndex (scratch p) p.memory

def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 2 (.i32 (scratch p))}
def afterFrame (frame : CallFrame) (p : Layout) := InterfaceLazyTail.afterFrame (reservedFrame frame p) (tailLayout p)
def after (s : Store NearState) (op : Nat) (p : Layout) := InterfaceLazyTail.after (initialized s op p) op (tailLayout p)

/-- Only initial structural facts and native bounds for the actual sequential
writes. The old status condition is a real load, rather than an execution oracle. -/
structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) : Prop where
  module : s.modules[frame.inst]? = some p.mi
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  tableIndex : p.mi.tableAddrs[0]? = some p.tableAddress
  table : s.tables[p.tableAddress]? = some p.table
  element : p.table.elems[p.location.toNat]? = some (.func p.initializerAddress)
  signature : p.mi.types[0]? = some WNear.Binary.InterfaceInitialize.signature
  initializer : s.funcs[p.initializerAddress]? = some (.wasm WNear.Binary.InterfaceInitialize.signature frame.inst WNear.Binary.InterfaceInitialize.function)
  cell : frame.locals[0]? = some (.i32 p.cell)
  location : frame.locals[1]? = some (.i32 p.location)
  localSize : 5 ≤ frame.locals.size
  initializerBound : (scratch p).toNat + 8 ≤ p.memory.byteSize
  depth : callers.length + 1 < limits.maxCallDepth
  tail : InterfaceLazyTail.Bounds (tailLayout p)

/-- The complete deployed lazy body, including reserve48, actual initializer
indirect call, all payload/status writes, empty-old-state branch and restore48. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s limits frame callers p)
    (hc : s.host.gas.Credits (70 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits
      (base.toArray.push (.i32 (p.cell + 4))) (afterFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 63) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceLazy.body ++ code))) (70 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let r := reserved s op p
  let i := initialized s op p
  let updated := reservedFrame frame p
  have h2 : 2 < frame.locals.size := by have hn := hr.localSize; omega
  have hcell : updated.locals[0]? = some (.i32 p.cell) := by
    simpa only [updated, reservedFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0)] using hr.cell
  have hlocation : updated.locals[1]? = some (.i32 p.location) := by
    simpa only [updated, reservedFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1)] using hr.location
  have hs : updated.locals[2]? = some (.i32 (scratch p)) := by
    simp only [updated, reservedFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt h2]
  have hn : 5 ≤ updated.locals.size := by simpa only [updated, reservedFrame, Array.size_set!] using hr.localSize
  have rm : r.modules[updated.inst]? = some p.mi := by simpa only [r, reserved, setGlobal, paid, chargedStore, updated, reservedFrame] using hr.module
  have rmem : r.mems[p.memoryIndex]? = some p.memory := by simpa only [r, reserved, setGlobal, paid, chargedStore] using hr.memory
  have rt : r.tables[p.tableAddress]? = some p.table := by simpa only [r, reserved, setGlobal, paid, chargedStore] using hr.table
  have rf : r.funcs[p.initializerAddress]? = some (.wasm WNear.Binary.InterfaceInitialize.signature updated.inst WNear.Binary.InterfaceInitialize.function) := by
    simpa only [r, reserved, setGlobal, paid, chargedStore, updated, reservedFrame] using hr.initializer
  have rg : r.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    simp only [r, reserved, setGlobal, paid, chargedStore, Array.getElem?_modify, hr.global, Option.map_some, ↓reduceIte]
  have fields := InterfaceLazyPrefix.after_resources r op p.memoryIndex (scratch p) p.memory
  have im : i.modules[updated.inst]? = some p.mi := by
    have h := congrArg (fun v => v.modules) fields
    simp only at h
    change i.modules = r.modules at h
    rw [h]; exact rm
  have ig : i.globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    have h := congrArg (fun v => v.globals) fields
    simp only at h
    change i.globals = r.globals at h
    rw [h]; exact rg
  have imem := InterfaceLazyPrefix.after_memory r op p.memoryIndex (scratch p) p.memory rmem
  have cr : r.host.gas.Credits (65 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have ci : i.host.gas.Credits (50 * op + rest) := InterfaceLazyPrefix.after_credits r op p.memoryIndex (50 * op + rest) (scratch p) p.memory
    (cr.mono (by omega))
  have tailNext : WP cfg fuel (.next (atCode (InterfaceLazyTail.after i cfg.regularOpCost (tailLayout p)) limits
      (base.toArray.push (.i32 ((tailLayout p).cell + 4))) (InterfaceLazyTail.afterFrame updated (tailLayout p)) callers code)) rest post := by
    simpa only [after, afterFrame, i, updated, op, tailLayout] using hnext
  have tail := InterfaceLazyTail.wp_tail cfg fuel rest i limits base.toArray updated callers code (tailLayout p) post
    hcell hs hn im hr.memoryIndex hr.globalIndex ig imem hr.tail ci tailNext
  have prefixNext : WP cfg (fuel + 51) (.next (atCode (InterfaceLazyPrefix.after r cfg.regularOpCost p.memoryIndex (scratch p) p.memory)
      limits base.toArray updated callers ((WNear.Binary.InterfaceLazy.exchange64 ++ WNear.Binary.InterfaceLazy.exchange32 ++
        WNear.Binary.InterfaceLazy.status ++ WNear.Binary.InterfaceLazy.saveOld ++ WNear.Binary.InterfaceLazy.result ++
        WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code))) (50 * cfg.regularOpCost + rest) post := by
    simpa only [i, initialized, r, op] using tail
  have initRule := InterfaceLazyPrefix.wp_initialize cfg (fuel + 51) (50 * cfg.regularOpCost + rest) r limits base updated callers _
    (scratch p) p.location p.mi p.tableAddress p.initializerAddress p.memoryIndex p.table p.memory post hs hlocation rm
    hr.tableIndex rt hr.element hr.signature rf hr.memoryIndex rmem hr.initializerBound hr.depth (cr.mono (by dsimp [op]; omega)) prefixNext
  have reserveNext : WP cfg (fuel + 58) (.next (atCode (setGlobal (paid s cfg.regularOpCost 5) p.globalIndex (.i32 (p.sp - 48))) limits base.toArray
      {frame with locals := frame.locals.set! 2 (.i32 (p.sp - 48))} callers
      ((WNear.Binary.InterfaceLazy.initCall ++ WNear.Binary.InterfaceLazy.exchange64 ++ WNear.Binary.InterfaceLazy.exchange32 ++
        WNear.Binary.InterfaceLazy.status ++ WNear.Binary.InterfaceLazy.saveOld ++ WNear.Binary.InterfaceLazy.result ++
        WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code))) (65 * cfg.regularOpCost + rest) post := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, List.append_assoc,
      show 15 * cfg.regularOpCost + (50 * cfg.regularOpCost + rest) = 65 * cfg.regularOpCost + rest by omega,
      r, reserved, updated, reservedFrame, scratch, op] using initRule
  have result := InterfaceStack.wp_reserve cfg (fuel + 58) (65 * cfg.regularOpCost + rest) s limits base.toArray frame callers _ p.mi p.globalIndex p.global
    p.sp 2 48 post hr.module hr.globalIndex hr.global hr.sp (hc.mono (by omega)) reserveNext
  have gas : 5 * cfg.regularOpCost + (65 * cfg.regularOpCost + rest) = 70 * cfg.regularOpCost + rest := by omega
  rw [gas] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, WNear.Binary.InterfaceLazy.body, WNear.Binary.InterfaceLazy.reserve, List.append_assoc] using result

end WNear.Proofs.InterfaceLazyComplete
