import Proofs.PanicHookSetPrefix
import Proofs.PanicHookSetSuffix

/-! Actual f822 on the first-install path. The slow initialization and old-hook
cleanup suffixes are skipped by original snapshot predicates, not execution assumptions. -/
namespace WNear.Proofs.PanicHookSet
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

/-- All data premises refer to the original memory snapshot. -/
structure Ready (s : Store NearState) (frame : CallFrame) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (receiver vtable : UInt32) : Prop where
  module : s.modules[frame.inst]? = some mi
  indexLookup : mi.memAddrs[0]? = some index
  memoryLookup : s.mems[index]? = some memory
  receiver : frame.locals[0]? = some (.i32 receiver)
  vtable : frame.locals[1]? = some (.i32 vtable)
  locals : 3 ≤ frame.locals.size
  wf : memory.wf
  span : 1074936 ≤ memory.byteSize
  initial : readI32 memory 1074932 = 0
  unlocked : readI32 memory 1074920 = 0
  oldVtable : readI32 memory 1074928 = 0

/-- The real body, including all four entered blocks and explicit return.
It installs arbitrary new receiver/vtable words and charges exactly31op. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (receiver vtable : UInt32) (post : Post)
    (hr : Ready s frame mi index memory receiver vtable)
    (ha : frame.arity = 0) (hh : frame.height = base.length)
    (hc : s.host.gas.Credits (31 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index memory receiver vtable)
      limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 35) (.next (atCode s limits base.toArray frame (caller :: callers)
      WNear.Binary.PanicHookSet.body)) (31 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let outer := emptyBlockFrame frame base.toArray.size [.unreachable,.unreachable]
  let inner := emptyBlockFrame outer base.toArray.size WNear.Binary.PanicHookSet.rejected
  let pf := prefixFrame inner memory
  have ms := memory_spec memory receiver vtable hr.wf hr.span
  have hb := hr.span
  have cp : (lockPassed s op index memory).host.gas.Credits (19 * op + rest) := by
    rw [lockPassed_host]
    exact paid_credits s op 12 _ (hc.mono (by dsimp [op]; omega))
  have m7 : (paid (lockLoaded s op) op 3).mems[index]? = some memory := by
    simpa only [lockLoaded,init,paid,chargedStore] using hr.memoryLookup
  have hstore := storeI32_memory (paid (lockLoaded s op) op 3) index 1074920 memory 4294967295 m7
  have mp : (lockPassed s op index memory).mems[index]? = some (lockedMemory memory) := by
    simpa only [lockPassed,locked,stored,paid,chargedStore,lockedMemory] using hstore
  have pr : pf.locals[0]? = some (.i32 receiver) := by
    simpa only [pf,prefixFrame,inner,outer,emptyBlockFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0)] using hr.receiver
  have pv : pf.locals[1]? = some (.i32 vtable) := by
    simpa only [pf,prefixFrame,inner,outer,emptyBlockFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1)] using hr.vtable
  have hn : WP cfg fuel (.next (atCode
      (suffixAfter (lockPassed s op index memory) op index (lockedMemory memory) receiver vtable)
      limits base.toArray caller callers caller.code)) rest post := by
    simpa only [suffixAfter,suffixStored,suffixLoaded,finishAfter,finishUnlocked,finishWritten,finishLoaded,
      after,guarded,unlocked,receiverStored,receiverLoaded,vtableStored,vtableLoaded,receiverMemory,vtableMemory,op] using hnext
  have tail := wp_suffix cfg fuel rest (lockPassed s op index memory) limits base pf caller callers mi index
    (lockedMemory memory) receiver vtable post (by rw [lockPassed_modules]; exact hr.module) hr.indexLookup mp
    ms.1 (by rw [ms.2.1]; omega) pr pv
    (by simpa only [pf,prefixFrame,inner,outer,emptyBlockFrame,Array.size_set!] using hr.locals)
    (ms.2.2.1.trans hr.oldVtable)
    (by simpa only [pf,prefixFrame,inner,outer,emptyBlockFrame] using ha)
    (by simpa only [pf,prefixFrame,inner,outer,emptyBlockFrame] using hh)
    (cp.mono (by dsimp [op]; omega)) hn
  have next : WP cfg (fuel + 20) (.next (atCode (lockPassed s cfg.regularOpCost index memory)
      limits base.toArray (prefixFrame inner memory) (caller :: callers)
      (WNear.Binary.PanicHookSet.replaceVtable ++ WNear.Binary.PanicHookSet.replaceReceiver ++
        WNear.Binary.PanicHookSet.unlock ++ [.block .empty (WNear.Binary.PanicHookSet.dropGuard ++ WNear.Binary.PanicHookSet.dropSlow), .return])))
      (19 * cfg.regularOpCost + rest) post := by simpa only [pf,op] using tail
  have headProof := wp_prefix cfg (fuel + 20) (19 * cfg.regularOpCost + rest) s limits base.toArray inner
    (caller :: callers) _ mi index memory post hr.module hr.indexLookup hr.memoryLookup hr.span hr.initial hr.unlocked
    hr.locals (hc.mono (by omega)) next
  unfold WNear.Binary.PanicHookSet.body
  apply wp_block_empty cfg (fuel + 34) _ s limits base.toArray frame (caller :: callers) _ [.unreachable,.unreachable] post hc
  apply wp_block_empty cfg (fuel + 33) _ s limits base.toArray outer (caller :: callers) _ WNear.Binary.PanicHookSet.rejected post hc
  simpa only [WNear.Binary.PanicHookSet.accepted,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 12 * cfg.regularOpCost + (19 * cfg.regularOpCost + rest) = 31 * cfg.regularOpCost + rest by omega] using headProof

end WNear.Proofs.PanicHookSet
