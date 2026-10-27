import Proofs.InterfaceSetHead
import Proofs.InterfaceSetPrefix
import Proofs.InterfaceSetFrame
import Proofs.InterfaceSetCredits

/-! Actual initialized setter prefix through the full exclusive-borrow call. -/
namespace WNear.Proofs.InterfaceSetInitializedPrefix
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetState WNear.Proofs.InterfaceSetPhases
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP

def tail : List Instr := WNear.Binary.InterfaceSet.copyBorrow ++ WNear.Binary.InterfaceSet.guard ++
  WNear.Binary.InterfaceSet.install ++ WNear.Binary.InterfaceSet.release

/-- Enter the two real zero-result blocks without charging guest gas. -/
theorem wp_blocks (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (post : Post) (hc : s.host.gas.Credits rest)
    (hnext : WP cfg fuel (.next (atCode s limits stack (nested frame stack.size code) callers
      WNear.Binary.InterfaceSet.inner)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits stack frame callers
      (.block .empty ([.block .empty WNear.Binary.InterfaceSet.inner] ++ WNear.Binary.InterfaceSet.fallback) ::
        (WNear.Binary.InterfaceSet.epilogue ++ code)))) rest post := by
  have inner := wp_block_empty cfg fuel rest s limits stack
    (emptyBlockFrame frame stack.size (WNear.Binary.InterfaceSet.epilogue ++ code)) callers
    WNear.Binary.InterfaceSet.inner WNear.Binary.InterfaceSet.fallback post hc hnext
  have outerNext : WP cfg (fuel + 1) (.next (atCode s limits stack
      (emptyBlockFrame frame stack.size (WNear.Binary.InterfaceSet.epilogue ++ code)) callers
      ([.block .empty WNear.Binary.InterfaceSet.inner] ++ WNear.Binary.InterfaceSet.fallback))) rest post := inner
  have outer := wp_block_empty cfg (fuel + 1) rest s limits stack frame callers
    ([.block .empty WNear.Binary.InterfaceSet.inner] ++ WNear.Binary.InterfaceSet.fallback)
    (WNear.Binary.InterfaceSet.epilogue ++ code) post hc outerNext
  simpa only [Nat.add_assoc, Nat.reduceAdd] using outer

/-- The initialized lookup branch executes its linked565/468 and441/492/672
callees. The three extra array facts identify memory and SP after earlier writes. -/
theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s limits frame callers p)
    (hmemS : (savedArguments s cfg.regularOpCost p).mems[p.memoryIndex]? = some (savedMemory p))
    (hmemA : (arguments s cfg.regularOpCost p).mems[p.memoryIndex]? = some (savedMemory p))
    (hgA : (arguments s cfg.regularOpCost p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)})
    (hc : s.host.gas.Credits (121 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (acquired s cfg.regularOpCost p) limits base.toArray
      (nested (guardedFrame frame p) base.toArray.size code) callers tail)) rest post) :
    WP cfg (fuel + 85) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceSet.body ++ code))) (121 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let fs := nested (reservedFrame frame p) base.toArray.size code
  let fg := nested (guardedFrame frame p) base.toArray.size code
  have cs : (savedArguments s op p).host.gas.Credits (110 * op + rest) :=
    savedArguments_credits s op _ p (hc.mono (by dsimp [op]; omega))
  have ca : (arguments s op p).host.gas.Credits (71 * op + rest) :=
    arguments_credits s op _ p (hc.mono (by dsimp [op]; omega))
  have cS : Code (savedArguments s op p) p fs.inst := by
    simpa only [fs, nested, emptyBlockFrame, reservedFrame] using savedArguments_code s op p frame.inst hr.code
  have cA : Code (arguments s op p) p fg.inst := by
    simpa only [fg, nested, emptyBlockFrame, guardedFrame, reservedFrame] using arguments_code s op p frame.inst hr.code
  have hl : fs.locals[0]? = some (.i32 p.interface) := by
    simpa [fs, nested, emptyBlockFrame, reservedFrame] using hr.interfaceLocal
  have hs : fs.locals[3]? = some (.i32 (scratch p)) := by
    simp [fs, nested, emptyBlockFrame, reservedFrame, show 3 < frame.locals.size by have h := hr.localSize; omega]
  have hsizeFs : 4 ≤ fs.locals.size := by
    simpa only [fs, nested, emptyBlockFrame, reservedFrame, Array.size_set!] using hr.localSize
  have links : InterfaceBorrow.Links (arguments s op p) p.mi fg.inst :=
    ⟨cA.module, ⟨672, cA.swapIndex, cA.swapFunction⟩, ⟨492, cA.takeIndex, cA.takeFunction⟩⟩
  have hw1 := writeI32_spec p.memory ((scratch p).toNat + 20) p.vtable hr.memoryWf hr.saveFirstBound
  have hw2 := writeI32_spec (writeI32 p.memory ((scratch p).toNat + 20) p.vtable)
    ((scratch p).toNat + 16) p.receiver hw1.1 hr.saveSecondBound
  have hwf : (savedMemory p).wf := hw2.1
  have call := InterfaceBorrow.wp_call_acquire cfg fuel rest (arguments s op p) limits base fg callers tail
    (scratch p) (scratch p + 8) 1074904 1055120 p.mi 441 p.globalIndex p.memoryIndex
    {p.global with value := .i32 (scratch p)} (savedMemory p) post links cA.acquireIndex cA.acquireFunction
    cA.globalIndex hgA rfl cA.memoryIndex hmemA hwf hr.cellBound hr.acquireOutBound hr.cellEmpty (by decide) hr.depth ca
  have callNext : WP cfg fuel (.next (atCode
      (InterfaceBorrow.calledAcquireStore (arguments s op p) op p.globalIndex p.memoryIndex
        (scratch p) (scratch p + 8) 1074904 (savedMemory p)) limits base.toArray fg callers tail)) rest post := hnext
  have called := call callNext
  have headNext : WP cfg (fuel + 47) (.next (atCode (InterfaceSetHead.after (savedArguments s op p) op) limits
      (base ++ [Value.i32 (scratch p + 8), .i32 1074904, .i32 1055120]).toArray
      (InterfaceSetHead.guarded fs) callers (.call 441 :: tail))) (71 * op + rest) post := by
    simpa only [InterfaceSetHead.after, InterfaceSetHead.looked, arguments, looked, lookupBefore,
      InterfaceSetHead.guarded, fs, fg, nested, emptyBlockFrame, guardedFrame, reservedFrame, op] using called
  have head := InterfaceSetHead.wp_head cfg (fuel + 47) (71 * op + rest) (savedArguments s op p)
    limits base fs callers tail p (savedMemory p) post cS hl hs hsizeFs hmemS hr.interfaceBound hr.interfaceRead
    hr.threadBound hr.threadStatus (by have h := hr.depth; omega) (cs.mono (by omega)) headNext
  have inner : WP cfg (fuel + 72) (.next (atCode (savedArguments s op p) limits base.toArray fs callers
      WNear.Binary.InterfaceSet.inner)) (110 * op + rest) post := by
    simpa only [WNear.Binary.InterfaceSet.inner, tail, List.append_assoc, Nat.add_assoc, Nat.reduceAdd,
      show 39 * cfg.regularOpCost + (71 * op + rest) = 110 * op + rest by dsimp [op]; omega] using head
  have outerBlock := wp_blocks cfg (fuel + 72) (110 * op + rest) (savedArguments s op p) limits base.toArray
    (reservedFrame frame p) callers code post cs inner
  have setup := InterfaceSetPrefix.wp_setup cfg ((fuel + 72) + 2) (110 * op + rest) s limits base.toArray frame callers
    (.block .empty ([.block .empty WNear.Binary.InterfaceSet.inner] ++ WNear.Binary.InterfaceSet.fallback) ::
      (WNear.Binary.InterfaceSet.epilogue ++ code)) p post hr.receiverLocal hr.vtableLocal hr.localSize hr.code
    hr.global hr.sp hr.memory hr.saveFirstBound hr.saveSecondBound (hc.mono (by dsimp [op]; omega)) outerBlock
  have fe : fuel + 72 + 2 + 11 = fuel + 85 := by omega
  have ge : 11 * cfg.regularOpCost + (110 * op + rest) = 121 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have ce : WNear.Binary.InterfaceSet.prologue ++ WNear.Binary.InterfaceSet.saveArguments ++
      (.block .empty ([.block .empty WNear.Binary.InterfaceSet.inner] ++ WNear.Binary.InterfaceSet.fallback) ::
        (WNear.Binary.InterfaceSet.epilogue ++ code)) = WNear.Binary.InterfaceSet.body ++ code := by
    simp only [WNear.Binary.InterfaceSet.body, List.append_assoc, List.cons_append, List.nil_append]
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fe ge ce setup

end WNear.Proofs.InterfaceSetInitializedPrefix
