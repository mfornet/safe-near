import Proofs.StateReadRegisterOuterState
import Proofs.StateReadRegisterOuterSteps
import Proofs.InterfaceStack

/-! Actual523 reserve48, register save and524 argument setup. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem wp_setup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (h1 : frame.locals[1]?=some (.i64 p.register)) (hs : 3≤frame.locals.size)
    (hm : s.modules[frame.inst]?=some p.mi) (hi : p.mi.memAddrs[0]?=some p.memoryIndex)
    (hmem : s.mems[p.memoryIndex]?=some p.memory) (hgi : p.mi.globalAddrs[0]?=some p.globalIndex)
    (hg : s.globals[p.globalIndex]?=some p.global523) (hv : p.global523.value=.i32 p.sp523)
    (hb : (scratch p).toNat+24+8≤p.memory.byteSize)
    (hc : s.host.gas.Credits (12*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (lengthArguments s cfg.regularOpCost p) limits
      (base++[Value.i32 (scratch p+8),.i64 p.register]).toArray (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+12) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateReadRegisterOuter.reserve++WNear.Binary.StateReadRegisterOuter.saveRegister++WNear.Binary.StateReadRegisterOuter.lengthArguments++code)))
      (12*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedFrame frame p
  have r2 : rf.locals[2]?=some (.i32 (scratch p)) := by simp [rf,reservedFrame,show 2<frame.locals.size by omega]
  have r1 : rf.locals[1]?=some (.i64 p.register) := by simp [rf,reservedFrame,h1]
  have arr : (base++[Value.i32 (scratch p+8),.i64 p.register]).toArray=
      (base.toArray.push (.i32 (scratch p+8))).push (.i64 p.register) := by apply Array.toList_inj.mp;simp
  have an : WP cfg fuel (.next (atCode (paid (registerStore s op p) op 4) limits
      ((base.toArray.push (.i32 (scratch p+8))).push (.i64 p.register)) rf callers code)) rest post := by
    simpa only [lengthArguments,arr,rf,op] using hnext
  have ca : (registerStore s op p).host.gas.Credits (4*op+rest) := by
    simpa only [registerStore,reserved,storeI64_host,setGlobal,paid,chargedStore] using
      paid_credits s op 8 (4*op+rest) (hc.mono (by dsimp [op];omega))
  have args := wp_length_arguments cfg fuel rest (registerStore s op p) limits base.toArray rf callers code (scratch p) p.register post r2 r1 ca an
  have rm : (reserved s op p).modules[rf.inst]?=some p.mi := by simpa only [reserved,paid,chargedStore,setGlobal,rf,reservedFrame] using hm
  have re : (reserved s op p).mems[p.memoryIndex]?=some p.memory := by simpa only [reserved,paid,chargedStore,setGlobal] using hmem
  have sn : WP cfg (fuel+4) (.next (atCode (saved (reserved s op p) op p.memoryIndex p.memory (scratch p) p.register)
      limits base.toArray rf callers (WNear.Binary.StateReadRegisterOuter.lengthArguments++code))) (4*op+rest) post := by
    simpa only [saved,registerStore,op] using args
  have save := wp_save_register cfg (fuel+4) (4*op+rest) (reserved s op p) limits base.toArray rf callers
    (WNear.Binary.StateReadRegisterOuter.lengthArguments++code) (scratch p) p.register p.mi p.memoryIndex p.memory post r2 r1 rm hi re hb
    (by simpa only [reserved,setGlobal] using paid_credits s op 5 (3*op+(4*op+rest)) (hc.mono (by dsimp [op];omega))) sn
  have rn : WP cfg ((fuel+4)+3) (.next (atCode (setGlobal (paid s op 5) p.globalIndex (.i32 (p.sp523-48))) limits base.toArray
      {frame with locals:=frame.locals.set! 2 (.i32 (p.sp523-48))} callers
      (WNear.Binary.StateReadRegisterOuter.saveRegister++WNear.Binary.StateReadRegisterOuter.lengthArguments++code))) (3*op+(4*op+rest)) post := by
    simpa only [reserved,rf,reservedFrame,scratch,List.append_assoc] using save
  have reserve := InterfaceStack.wp_reserve cfg ((fuel+4)+3) (3*op+(4*op+rest)) s limits base.toArray frame callers
    (WNear.Binary.StateReadRegisterOuter.saveRegister++WNear.Binary.StateReadRegisterOuter.lengthArguments++code)
    p.mi p.globalIndex p.global523 p.sp523 2 48 post hm hgi hg hv (hc.mono (by dsimp [op];omega)) rn
  have ce : 5*cfg.regularOpCost+(3*op+(4*op+rest))=12*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at reserve
  simpa only [WNear.Binary.StateReadRegisterOuter.reserve,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using reserve
end WNear.Proofs.StateReadRegisterOuter
