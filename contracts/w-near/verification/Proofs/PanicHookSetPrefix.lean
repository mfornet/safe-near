import Proofs.PanicHookSetFinish

/-! Opaque-store first-install prefix: enter guard, load/hold lock, and accept it. -/
namespace WNear.Proofs.PanicHookSet
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def prefixFrame (frame : CallFrame) (memory : Memory) :=
  {frame with locals := frame.locals.set! 2 (.i32 (readI32 memory 1074920))}

theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : 1074936 ≤ memory.byteSize)
    (hz : readI32 memory 1074932 = 0) (hl : readI32 memory 1074920 = 0)
    (hsize : 3 ≤ frame.locals.size)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (lockPassed s cfg.regularOpCost index memory)
      limits stack (prefixFrame frame memory) callers code)) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits stack frame callers
      ([.block .empty (WNear.Binary.PanicHookSet.initializationGuard ++ WNear.Binary.PanicHookSet.initializationSlow)] ++
        WNear.Binary.PanicHookSet.lock ++ code))) (12 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have c4 : (init s op).host.gas.Credits (8 * op + rest) := by rw [init_host]; exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  have c7 : (lockLoaded s op).host.gas.Credits (5 * op + rest) := by rw [lockLoaded_host]; exact paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))
  have c10 : (locked s op index memory).host.gas.Credits (2 * op + rest) := by rw [locked_host]; exact paid_credits s op 10 _ (hc.mono (by dsimp [op]; omega))
  have m4 : (init s op).mems[index]? = some memory := by simpa only [init,paid,chargedStore] using hmem
  have m7 : (lockLoaded s op).mems[index]? = some memory := by simpa only [lockLoaded,paid,chargedStore] using m4
  have hzero : (prefixFrame frame memory).locals[2]? = some (.i32 0) := by
    have h2 : 2 < frame.locals.size := by omega
    simp only [prefixFrame,hl,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt h2]
  rw [show 12 * cfg.regularOpCost + rest = 4 * cfg.regularOpCost + (8 * op + rest) by dsimp [op]; omega]
  apply wp_memory_guard cfg (fuel + 8) _ s limits stack frame callers WNear.Binary.PanicHookSet.initializationSlow _
    1074932 mi index memory post hm hi hmem (by omega) hz (hc.mono (by dsimp [op]; omega))
  rw [show 8 * op + rest = 3 * cfg.regularOpCost + (5 * op + rest) by dsimp [op]; omega]
  apply wp_load_save cfg (fuel + 5) _ (init s op) limits stack frame callers _ 1074920 2 mi index memory post
    (by rw [init_modules]; exact hm) hi m4 (by omega) (c4.mono (by dsimp [op]; omega))
  rw [show 5 * op + rest = 3 * cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_store_const cfg (fuel + 2) _ (lockLoaded s op) limits stack (prefixFrame frame memory) callers _
    1074920 4294967295 mi index memory post (by rw [lockLoaded_modules]; exact hm) hi m7 (by omega)
    (c7.mono (by dsimp [op]; omega))
  have next : WP cfg fuel (.next (atCode (paid (locked s op index memory) op 2)
      limits stack (prefixFrame frame memory) callers code)) rest post := by simpa only [lockPassed,op] using hnext
  have r := wp_local_branch_zero cfg fuel rest (locked s op index memory) limits stack (prefixFrame frame memory)
    callers code 2 1 post hzero (c10.mono (by dsimp [op]; omega)) next
  simpa only [op,locked,List.append_eq,List.cons_append,List.nil_append] using r

end WNear.Proofs.PanicHookSet
