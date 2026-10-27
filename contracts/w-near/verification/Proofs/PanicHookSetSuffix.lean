import Proofs.PanicHookSetFinish

/-! The old vtable is snapshotted before replacement; its zero value selects
normal first installation independently of the new vtable word. -/
namespace WNear.Proofs.PanicHookSet
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def suffixLoaded (s : Store NearState) (op : Nat) := paid s op 3
def suffixStored (s : Store NearState) (op index : Nat) (memory : Memory) (vtable : UInt32) := stored (suffixLoaded s op) op index 1074928 memory vtable
def suffixAfter (s : Store NearState) (op index : Nat) (memory : Memory) (receiver vtable : UInt32) := finishAfter (suffixStored s op index memory vtable) op index (writeI32 memory 1074928 vtable) receiver

theorem wp_suffix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (receiver vtable : UInt32) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hwf : memory.wf) (hb : 1074936 ≤ memory.byteSize)
    (hr : frame.locals[0]? = some (.i32 receiver)) (hv : frame.locals[1]? = some (.i32 vtable))
    (hsize : 3 ≤ frame.locals.size) (hz : readI32 memory 1074928 = 0)
    (ha : frame.arity = 0) (hh : frame.height = base.length)
    (hc : s.host.gas.Credits (19 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (suffixAfter s cfg.regularOpCost index memory receiver vtable)
      limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 20) (.next (atCode s limits base.toArray frame (caller :: callers)
      (WNear.Binary.PanicHookSet.replaceVtable ++ WNear.Binary.PanicHookSet.replaceReceiver ++ WNear.Binary.PanicHookSet.unlock ++
        [.block .empty (WNear.Binary.PanicHookSet.dropGuard ++ WNear.Binary.PanicHookSet.dropSlow), .return])))
      (19 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := {frame with locals := frame.locals.set! 2 (.i32 (readI32 memory 1074928))}
  have fr : f.locals[0]? = some (.i32 receiver) := by simpa only [f,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0)] using hr
  have fv : f.locals[1]? = some (.i32 vtable) := by simpa only [f,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1)] using hv
  have fz : f.locals[2]? = some (.i32 0) := by
    have h2 : 2 < frame.locals.size := by omega
    simp only [f,hz,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt h2]
  have c3 : (suffixLoaded s op).host.gas.Credits (16 * op + rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  have c6 : (suffixStored s op index memory vtable).host.gas.Credits (13 * op + rest) := by
    simpa only [suffixStored,suffixLoaded,stored,storeI32,paid,chargedStore] using paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  have m3 : (suffixLoaded s op).mems[index]? = some memory := by simpa only [suffixLoaded,paid,chargedStore] using hmem
  have m3p : (paid (suffixLoaded s op) op 3).mems[index]? = some memory := by simpa only [paid,chargedStore] using m3
  have m6 : (suffixStored s op index memory vtable).mems[index]? = some (writeI32 memory 1074928 vtable) := by
    simpa only [suffixStored,stored] using storeI32_memory (paid (suffixLoaded s op) op 3) index 1074928 memory vtable m3p
  have spec := writeI32_spec memory 1074928 vtable hwf (by omega)
  have hn : WP cfg fuel (.next (atCode (finishAfter (suffixStored s op index memory vtable) op index
      (writeI32 memory 1074928 vtable) receiver) limits base.toArray caller callers caller.code)) rest post := by
    simpa only [suffixAfter,op] using hnext
  have tail := wp_finish cfg fuel rest (suffixStored s op index memory vtable) limits base f caller callers mi index
    (writeI32 memory 1074928 vtable) receiver post (by simpa only [suffixStored,suffixLoaded,stored,storeI32,paid,chargedStore] using hm)
    hi m6 spec.1 (by rw [spec.2.1]; omega) fr fz (by simpa only [f] using ha) (by simpa only [f] using hh)
    (c6.mono (by dsimp [op]; omega)) hn
  unfold WNear.Binary.PanicHookSet.replaceVtable
  rw [show 19 * cfg.regularOpCost + rest = 3 * cfg.regularOpCost + (16 * op + rest) by dsimp [op]; omega]
  apply wp_load_save cfg (fuel + 17) _ s limits base.toArray frame (caller :: callers) _ 1074928 2 mi index memory post hm hi hmem (by omega) (hc.mono (by dsimp [op]; omega))
  rw [show 16 * op + rest = 3 * cfg.regularOpCost + (13 * op + rest) by dsimp [op]; omega]
  apply wp_store_local cfg (fuel + 14) _ (suffixLoaded s op) limits base.toArray f (caller :: callers) _ 1074928 1 vtable mi index memory post fv
    (by simpa only [suffixLoaded,paid,chargedStore] using hm) hi m3 (by omega) (c3.mono (by dsimp [op]; omega))
  simpa only [op,suffixStored,WNear.Binary.PanicHookSet.replaceReceiver,List.append_eq,List.cons_append,List.nil_append] using tail

end WNear.Proofs.PanicHookSet
