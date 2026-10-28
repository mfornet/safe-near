import Proofs.StateReadStorageOuterPrepare

/-! Actual548 prefix before its four nested blocks: reserve and both key stores. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem wp_setup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 p.keyPtr)) (h2 : frame.locals[2]?=some (.i32 p.keyLen))
    (hs : 4≤frame.locals.size) (hm : s.modules[frame.inst]?=some p.mi)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hgi : p.mi.globalAddrs[0]?=some p.globalIndex)
    (hg : s.globals[p.globalIndex]?=some p.global548) (hv : p.global548.value=.i32 p.sp548)
    (hwf : p.memory.wf) (hb : (scratch p).toNat+16≤p.memory.byteSize)
    (hc : s.host.gas.Credits (11*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (setupStore s cfg.regularOpCost p) limits base.toArray (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+11) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateReadStorageOuter.reserve++WNear.Binary.StateReadStorageOuter.saveLength++WNear.Binary.StateReadStorageOuter.savePointer++code)))
      (11*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedFrame frame p
  have r3 : rf.locals[3]?=some (.i32 (scratch p)) := by simp [rf,reservedFrame,show 3<frame.locals.size by omega]
  have r1 : rf.locals[1]?=some (.i32 p.keyPtr) := by simp [rf,reservedFrame,h1]
  have r2 : rf.locals[2]?=some (.i32 p.keyLen) := by simp [rf,reservedFrame,h2]
  have rm : (reserved s op p).modules[rf.inst]?=some p.mi := by simpa only [reserved,paid,chargedStore,setGlobal,rf,reservedFrame] using hm
  have re : (reserved s op p).mems[p.memoryIndex]?=some p.memory := by simpa only [reserved,paid,chargedStore,setGlobal] using hmem
  have sn : WP cfg fuel (.next (atCode (savedKey (reserved s op p) op p.memoryIndex p.memory (scratch p) p.keyPtr p.keyLen)
      limits base.toArray rf callers code)) rest post := by
    simpa only [setupStore,highStore,highMemory,savedKey,savedWord,op] using hnext
  have cr : (reserved s op p).host.gas.Credits (6*op+rest) := by
    simpa only [reserved,setGlobal] using paid_credits s op 5 (6*op+rest) (hc.mono (by dsimp [op];omega))
  have saves := wp_save_key cfg fuel rest (reserved s op p) limits base.toArray rf callers code
    (scratch p) p.keyPtr p.keyLen p.mi p.memoryIndex p.memory post r3 r1 r2 rm hi re hwf hb cr sn
  have rn : WP cfg (fuel+6) (.next (atCode (setGlobal (paid s op 5) p.globalIndex (.i32 (p.sp548-32))) limits base.toArray
      {frame with locals:=frame.locals.set! 3 (.i32 (p.sp548-32))} callers
      (WNear.Binary.StateReadStorageOuter.saveLength++WNear.Binary.StateReadStorageOuter.savePointer++code))) (6*op+rest) post := by
    simpa only [reserved,rf,reservedFrame,scratch,List.append_assoc] using saves
  have reserve := InterfaceStack.wp_reserve cfg (fuel+6) (6*op+rest) s limits base.toArray frame callers
    (WNear.Binary.StateReadStorageOuter.saveLength++WNear.Binary.StateReadStorageOuter.savePointer++code)
    p.mi p.globalIndex p.global548 p.sp548 3 32 post hm hgi hg hv (hc.mono (by dsimp [op];omega)) rn
  have ce : 5*cfg.regularOpCost+(6*op+rest)=11*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at reserve
  simpa only [WNear.Binary.StateReadStorageOuter.reserve,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using reserve
end WNear.Proofs.StateReadStorageOuter
