import Proofs.InterfaceSetInitializedPrefix

/-! Shared real setter setup and two nested blocks, independent of lookup mode. -/
namespace WNear.Proofs.InterfaceSetSetup
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.InterfaceSetState
set_option maxRecDepth 16384
set_option maxHeartbeats 200000
attribute [local irreducible] WP

/-- Eleven charged instructions and two free block entries. -/
theorem wp_setup_blocks (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hreceiver : frame.locals[1]? = some (.i32 p.receiver)) (hvtable : frame.locals[2]? = some (.i32 p.vtable))
    (hsize : 4 ≤ frame.locals.size) (hcode : Code s p frame.inst)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp)
    (hm : s.mems[p.memoryIndex]? = some p.memory)
    (hb1 : (scratch p).toNat + 20 + 4 ≤ p.memory.byteSize)
    (hb2 : (scratch p).toNat + 16 + 4 ≤ (writeI32 p.memory ((scratch p).toNat + 20) p.vtable).byteSize)
    (hc : s.host.gas.Credits (11 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (savedArguments s cfg.regularOpCost p) limits base.toArray
      (nested (reservedFrame frame p) base.toArray.size code) callers WNear.Binary.InterfaceSet.inner)) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceSet.body ++ code))) (11 * cfg.regularOpCost + rest) post := by
  have cs := InterfaceSetPhases.savedArguments_credits s cfg.regularOpCost rest p hc
  have blocks := InterfaceSetInitializedPrefix.wp_blocks cfg fuel rest (savedArguments s cfg.regularOpCost p)
    limits base.toArray (reservedFrame frame p) callers code post cs hnext
  have result := InterfaceSetPrefix.wp_setup cfg (fuel + 2) rest s limits base.toArray frame callers
    (.block .empty ([.block .empty WNear.Binary.InterfaceSet.inner] ++ WNear.Binary.InterfaceSet.fallback) ::
      (WNear.Binary.InterfaceSet.epilogue ++ code)) p post hreceiver hvtable hsize hcode hg hsp hm hb1 hb2 hc blocks
  have fe : fuel + 2 + 11 = fuel + 13 := by omega
  have ce : WNear.Binary.InterfaceSet.prologue ++ WNear.Binary.InterfaceSet.saveArguments ++
      (.block .empty ([.block .empty WNear.Binary.InterfaceSet.inner] ++ WNear.Binary.InterfaceSet.fallback) ::
        (WNear.Binary.InterfaceSet.epilogue ++ code)) = WNear.Binary.InterfaceSet.body ++ code := by
    simp only [WNear.Binary.InterfaceSet.body, List.append_assoc, List.cons_append, List.nil_append]
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fe rfl ce result

end WNear.Proofs.InterfaceSetSetup
