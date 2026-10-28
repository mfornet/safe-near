import Proofs.StateDecodeBorshReadPhases
import Proofs.StateReadStorageOuterSave
import Proofs.InterfaceStack

/-! Actual548 prefix before its four nested blocks: reserve and both key stores. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open StateReadStorageOuter (wp_save_key savedKey savedWord)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def saveLengthCode:Expr:=[.local_get 3,.local_get 2,.store .i32 none {align:=2,offset:=12}]
def savePointerCode:Expr:=[.local_get 3,.local_get 1,.store .i32 none {align:=2,offset:=8}]

private theorem setup_code:WNear.Binary.StateDecodeBorshRead.setup=[.global_get 0,.i32_const 144,.i32_binop .sub,.local_tee 3,.global_set 0]:=by rfl
private theorem length_code:WNear.Binary.StateReadStorageOuter.saveLength=saveLengthCode:=by rfl
private theorem pointer_code:WNear.Binary.StateReadStorageOuter.savePointer=savePointerCode:=by rfl

theorem wp_setup (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 p.pointer)) (h2 : frame.locals[2]?=some (.i32 p.length))
    (hs : 4≤frame.locals.size) (hm : s.modules[frame.inst]?=some p.mi)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hgi : p.mi.globalAddrs[0]?=some p.globalIndex)
    (hg : s.globals[p.globalIndex]?=some p.global161) (hv : p.global161.value=.i32 p.sp161)
    (hwf : p.memory.wf) (hb : (scratch p).toNat+16≤p.memory.byteSize)
    (hc : s.host.gas.Credits (11*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (sliceSaved s cfg.regularOpCost p) limits base.toArray (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+11) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodeBorshRead.setup++saveLengthCode++savePointerCode++code)))
      (11*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedFrame frame p
  have r3 : rf.locals[3]?=some (.i32 (scratch p)) := by simp [rf,reservedFrame,show 3<frame.locals.size by omega]
  have r1 : rf.locals[1]?=some (.i32 p.pointer) := by simp [rf,reservedFrame,h1]
  have r2 : rf.locals[2]?=some (.i32 p.length) := by simp [rf,reservedFrame,h2]
  have rm : (reserved s op p).modules[rf.inst]?=some p.mi := by simpa only [reserved,paid,chargedStore,setGlobal,rf,reservedFrame] using hm
  have re : (reserved s op p).mems[p.memoryIndex]?=some p.memory := by simpa only [reserved,paid,chargedStore,setGlobal] using hmem
  have sn : WP cfg fuel (.next (atCode (savedKey (reserved s op p) op p.memoryIndex p.memory (scratch p) p.pointer p.length)
      limits base.toArray rf callers code)) rest post := by
    simpa only [sliceSaved,highSaved,highSetupMemory,savedKey,savedWord,op] using hnext
  have cr : (reserved s op p).host.gas.Credits (6*op+rest) := by
    simpa only [reserved,setGlobal] using paid_credits s op 5 (6*op+rest) (hc.mono (by dsimp [op];omega))
  have saves := wp_save_key cfg fuel rest (reserved s op p) limits base.toArray rf callers code
    (scratch p) p.pointer p.length p.mi p.memoryIndex p.memory post r3 r1 r2 rm hi re hwf hb cr sn
  have rn : WP cfg (fuel+6) (.next (atCode (setGlobal (paid s op 5) p.globalIndex (.i32 (p.sp161-144))) limits base.toArray
      {frame with locals:=frame.locals.set! 3 (.i32 (p.sp161-144))} callers
      (saveLengthCode++savePointerCode++code))) (6*op+rest) post := by
    simpa only [reserved,rf,reservedFrame,scratch,List.append_assoc,length_code,pointer_code] using saves
  have reserve := InterfaceStack.wp_reserve cfg (fuel+6) (6*op+rest) s limits base.toArray frame callers
    (saveLengthCode++savePointerCode++code)
    p.mi p.globalIndex p.global161 p.sp161 3 144 post hm hgi hg hv (hc.mono (by dsimp [op];omega)) rn
  have ce : 5*cfg.regularOpCost+(6*op+rest)=11*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at reserve
  simpa only [setup_code,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using reserve
end WNear.Proofs.StateDecodeBorshRead
