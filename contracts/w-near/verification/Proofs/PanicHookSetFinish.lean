import Proofs.PanicHookSetState

/-! Opaque pre-store capsule for the actual final14steps of first installation. -/
namespace WNear.Proofs.PanicHookSet
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def finishLoaded (s : Store NearState) (op : Nat) := paid s op 3
def finishWritten (s : Store NearState) (op index : Nat) (memory : Memory) (receiver : UInt32) := stored (finishLoaded s op) op index 1074924 memory receiver
def finishUnlocked (s : Store NearState) (op index : Nat) (memory : Memory) (receiver : UInt32) := stored (finishWritten s op index memory receiver) op index 1074920 (writeI32 memory 1074924 receiver) 0
def finishAfter (s : Store NearState) (op index : Nat) (memory : Memory) (receiver : UInt32) := chargedStore (paid (finishUnlocked s op index memory receiver) op 3) op

theorem wp_finish (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (receiver : UInt32) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hwf : memory.wf) (hb : 1074936 ≤ memory.byteSize)
    (hr : frame.locals[0]? = some (.i32 receiver)) (hz : frame.locals[2]? = some (.i32 0))
    (ha : frame.arity = 0) (hh : frame.height = base.length)
    (hc : s.host.gas.Credits (13 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (finishAfter s cfg.regularOpCost index memory receiver)
      limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 14) (.next (atCode s limits base.toArray frame (caller :: callers)
      (WNear.Binary.PanicHookSet.replaceReceiver ++ WNear.Binary.PanicHookSet.unlock ++
        [.block .empty (WNear.Binary.PanicHookSet.dropGuard ++ WNear.Binary.PanicHookSet.dropSlow), .return])))
      (13 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := {frame with locals := frame.locals.set! 1 (.i32 (readI32 memory 1074924))}
  have fr : f.locals[0]? = some (.i32 receiver) := by
    simpa only [f,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0)] using hr
  have fz : f.locals[2]? = some (.i32 0) := by
    simpa only [f,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 2)] using hz
  have c3 : (finishLoaded s op).host.gas.Credits (10 * op + rest) := paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  have c6 : (finishWritten s op index memory receiver).host.gas.Credits (7 * op + rest) := by
    simpa only [finishWritten,finishLoaded,stored,storeI32,paid,chargedStore] using paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  have c9 : (finishUnlocked s op index memory receiver).host.gas.Credits (4 * op + rest) := by
    simpa only [finishUnlocked,finishWritten,finishLoaded,stored,storeI32,paid,chargedStore] using paid_credits s op 9 _ (hc.mono (by dsimp [op]; omega))
  have c12 : (paid (finishUnlocked s op index memory receiver) op 3).host.gas.Credits (op + rest) :=
    paid_credits (finishUnlocked s op index memory receiver) op 3 _ (c9.mono (by omega))
  have m3 : (finishLoaded s op).mems[index]? = some memory := by simpa only [finishLoaded,paid,chargedStore] using hmem
  have m3p : (paid (finishLoaded s op) op 3).mems[index]? = some memory := by simpa only [paid,chargedStore] using m3
  have m6 : (finishWritten s op index memory receiver).mems[index]? = some (writeI32 memory 1074924 receiver) := by
    simpa only [finishWritten,stored] using storeI32_memory (paid (finishLoaded s op) op 3) index 1074924 memory receiver m3p
  have spec := writeI32_spec memory 1074924 receiver hwf (by omega)
  unfold WNear.Binary.PanicHookSet.replaceReceiver
  rw [show 13 * cfg.regularOpCost + rest = 3 * cfg.regularOpCost + (10 * op + rest) by dsimp [op]; omega]
  apply wp_load_save cfg (fuel + 11) _ s limits base.toArray frame (caller :: callers) _ 1074924 1 mi index memory post hm hi hmem (by omega) (hc.mono (by dsimp [op]; omega))
  rw [show 10 * op + rest = 3 * cfg.regularOpCost + (7 * op + rest) by dsimp [op]; omega]
  apply wp_store_local cfg (fuel + 8) _ (finishLoaded s op) limits base.toArray f (caller :: callers) _ 1074924 0 receiver mi index memory post fr
    (by simpa only [finishLoaded,paid,chargedStore] using hm) hi m3 (by omega) (c3.mono (by dsimp [op]; omega))
  rw [show 7 * op + rest = 3 * cfg.regularOpCost + (4 * op + rest) by dsimp [op]; omega]
  apply wp_store_const cfg (fuel + 5) _ (finishWritten s op index memory receiver) limits base.toArray f (caller :: callers) _ 1074920 0 mi index (writeI32 memory 1074924 receiver) post
    (by simpa only [finishWritten,finishLoaded,stored,storeI32,paid,chargedStore] using hm) hi m6 (by rw [spec.2.1]; omega) (c6.mono (by dsimp [op]; omega))
  rw [show 4 * op + rest = 3 * cfg.regularOpCost + (cfg.regularOpCost + rest) by dsimp [op]; omega]
  apply wp_local_guard cfg (fuel + 1) _ (finishUnlocked s op index memory receiver) limits base.toArray f (caller :: callers) WNear.Binary.PanicHookSet.dropSlow [.return] 2 post fz (c9.mono (by dsimp [op]; omega))
  have ret := ValueReturnLazyLookup.wp_return_wasm cfg fuel rest (paid (finishUnlocked s op index memory receiver) op 3)
    limits base [] f caller callers [] post (by simpa only [f,List.length_nil] using ha.symm) (by simpa only [f] using hh) c12
  have hn : WP cfg fuel (.next (atCode (chargedStore (paid (finishUnlocked s op index memory receiver) op 3) op)
      limits (base ++ []).toArray caller callers caller.code)) rest post := by
    simpa only [finishAfter,List.append_nil,op] using hnext
  have result := ret hn
  simpa only [List.append_nil,op] using result

end WNear.Proofs.PanicHookSet
