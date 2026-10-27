import Proofs.InterfaceSetState
import Proofs.InterfaceStack
import Proofs.ValueReturnOuterBody

/-! The exact eleven-instruction setup before the setter's nested blocks. -/
namespace WNear.Proofs.InterfaceSetPrefix
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetState WNear.Proofs.InterfaceSetBody
set_option maxRecDepth 16384
set_option maxHeartbeats 500000

theorem wp_setup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hl1 : frame.locals[1]? = some (.i32 p.receiver)) (hl2 : frame.locals[2]? = some (.i32 p.vtable))
    (hsize : 4 ≤ frame.locals.size) (hcode : Code s p frame.inst)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp)
    (hm : s.mems[p.memoryIndex]? = some p.memory)
    (hb1 : (scratch p).toNat + 20 + 4 ≤ p.memory.byteSize)
    (hb2 : (scratch p).toNat + 16 + 4 ≤ (writeI32 p.memory ((scratch p).toNat + 20) p.vtable).byteSize)
    (hc : s.host.gas.Credits (11 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (savedArguments s cfg.regularOpCost p) limits stack
      (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 11) (.next (atCode s limits stack frame callers
      (WNear.Binary.InterfaceSet.prologue ++ WNear.Binary.InterfaceSet.saveArguments ++ code)))
      (11 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let r := reserved s op p
  let f := reservedFrame frame p
  have cr : r.host.gas.Credits (6 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have h3 : 3 < frame.locals.size := by omega
  have hs : f.locals[3]? = some (.i32 (scratch p)) := by simp [f, reservedFrame, h3]
  have h1 : f.locals[1]? = some (.i32 p.receiver) := by simpa [f, reservedFrame] using hl1
  have h2 : f.locals[2]? = some (.i32 p.vtable) := by simpa [f, reservedFrame] using hl2
  have hmodule : r.modules[f.inst]? = some p.mi := by simpa only [r, reserved, f, reservedFrame, paid, chargedStore, setGlobal] using hcode.module
  have hmemory : r.mems[p.memoryIndex]? = some p.memory := by simpa only [r, reserved, paid, chargedStore, setGlobal] using hm
  have stores := wp_two_words cfg fuel rest r limits stack f callers code 3 2 1 20 16 (scratch p) p.vtable p.receiver p.mi p.memoryIndex p.memory post
    hs h2 h1 hmodule hcode.memoryIndex hmemory hb1 hb2 cr hnext
  have reserveRule := InterfaceStack.wp_reserve cfg (fuel + 6) (6 * op + rest) s limits stack frame callers
    (WNear.Binary.InterfaceSet.saveArguments ++ code) p.mi p.globalIndex p.global p.sp 3 32 post
    hcode.module hcode.globalIndex hg hsp (hc.mono (by dsimp [op]; omega))
  have reserveNext : WP cfg (fuel + 6) (.next (atCode r limits stack f callers
      (WNear.Binary.InterfaceSet.saveArguments ++ code))) (6 * op + rest) post := stores
  have result := reserveRule reserveNext
  have fuelEq : fuel + 6 + 5 = fuel + 11 := by omega
  have gasEq : 5 * cfg.regularOpCost + (6 * op + rest) = 11 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have codeEq : ([.global_get 0, .i32_const 32, .i32_binop .sub, .local_tee 3, .global_set 0] ++ (WNear.Binary.InterfaceSet.saveArguments ++ code)) =
      (WNear.Binary.InterfaceSet.prologue ++ WNear.Binary.InterfaceSet.saveArguments ++ code) := by simp only [WNear.Binary.InterfaceSet.prologue, List.append_assoc]
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits stack frame callers _ _ post fuelEq gasEq codeEq result

end WNear.Proofs.InterfaceSetPrefix
