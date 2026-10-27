import Proofs.AllocateFlaggedBody
import Binary.AllocateSearchEntry
import NearVM.MeteredWasmCall

/-! Actual typed580 call on the directly-fitting nonempty free-list branch. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode searchAfter searchFrame

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (15*op)
def callAfter (s : Store NearState) (op : Nat) (p : Layout) := searchAfter (entered s op) op p
def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.words,.i32 1,.i32 p.root,.i32 p.context,.i32 p.vtable,
      .i32 0,.i32 0,.i32 0,.i32 0,.i32 0,.i32 0,.i32 0,.i32 0,.i32 0],
   inst,arity:=1,height,labels:=[],code:=[]}

theorem entered_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (16*op+rest)) :
    (entered s op).host.gas.Credits rest := by
  have a := StorePair.charged_credits s op (15*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (15*op) rest a

theorem callAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (278*op+rest)) :
    (callAfter s op p).host.gas.Credits rest := by
  unfold callAfter
  exact searchAfter_credits _ op rest p (entered_credits s op _ (hc.mono (by omega)))

theorem searchFrame_shape (frame : CallFrame) (p : Layout) :
    (searchFrame frame p).arity=frame.arity ∧ (searchFrame frame p).height=frame.height ∧
    (searchFrame frame p).labels=frame.labels := by
  simp only [searchFrame,searchedFrame,initialFrame,finalFrame,mutateFrame,Allocate.resultFrame,controlFrame,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,
    splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame,candidateFrame,unitsFrame,prepareFrame,and_self]

/-- The real function activation, full235-step body, and normal one-value
return. All code/native premises concern the original state. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hn : Native p) (hcode : SearchCode s p frame.inst)
    (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hi : p.mi.funcAddrs[580]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.AllocateSearch.signature frame.inst WNear.Binary.Allocate.searchFunction))
    (hd : callers.length+2<limits.maxCallDepth) (hc : s.host.gas.Credits (278*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits
      (base++[Value.i32 (pointer p)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+240) (.next (atCode s limits (base++[Value.i32 p.words,.i32 1,.i32 p.root,.i32 p.context,.i32 p.vtable]).toArray
      frame callers (.call 580::code))) (278*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ca := entered_credits s op (262*op+rest) (hc.mono (by dsimp [op]; omega))
  have cf := callAfter_credits s op rest p hc
  have sh := searchFrame_shape leaf p
  have arity : [Value.i32 (pointer p)].length=(searchFrame leaf p).arity := by rw [sh.1]; rfl
  have height : (searchFrame leaf p).height=base.length := by rw [sh.2.1]; rfl
  have labels : (searchFrame leaf p).labels=[] := by rw [sh.2.2]; rfl
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p) limits (base++[Value.i32 (pointer p)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter s op p) limits base [.i32 (pointer p)] (searchFrame leaf p) saved callers post arity height labels cf leaveNext
  have arr : (base++[Value.i32 (pointer p)]).toArray=base.toArray.push (.i32 (pointer p)) := by apply Array.toList_inj.mp; simp
  have bn : WP cfg (fuel+1) (.next (atCode (searchAfter active op p) limits (base.toArray.push (.i32 (pointer p)))
      (searchFrame leaf p) (saved::callers) [])) rest post := by simpa only [callAfter,active,arr] using leave
  have codeActive : SearchCode active p leaf.inst := by
    constructor
    · exact hcode.toCode.transport s active p frame.inst rfl rfl rfl
    · exact hcode.sizeIndex
    · exact hcode.sizeFunction
  have memActive : active.mems[p.memoryIndex]?=some p.memory := hmem
  have body := wp_body cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] p post hn codeActive
    rfl rfl rfl rfl rfl (by simp [leaf,leafFrame]) memActive (by simpa only [List.length_cons] using hd) ca bn
  have callRule := wp_call_wasm cfg ((fuel+1)+238) (262*op+rest) s limits base
    [.i32 p.words,.i32 1,.i32 p.root,.i32 p.context,.i32 p.vtable] frame callers code 580 address p.mi
    WNear.Binary.AllocateSearch.signature frame.inst WNear.Binary.Allocate.searchFunction post hcode.module hi hf rfl (by omega)
  rw [WNear.Binary.AllocateSearch.activation] at callRule
  have arrays : #[Value.i32 p.words,Value.i32 1,Value.i32 p.root,Value.i32 p.context,Value.i32 p.vtable]++
      #[Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0]=
      (leafFrame frame.inst base.length p).locals := by apply Array.toList_inj.mp; simp [leafFrame]
  have next : WP cfg ((fuel+1)+238) (.next (wasmCallee active limits base frame callers code WNear.Binary.AllocateSearch.signature
      frame.inst WNear.Binary.Allocate.searchFunction [.i32 p.words,.i32 1,.i32 p.root,.i32 p.context,.i32 p.vtable])) (262*op+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateSearch.function_locals,WNear.Binary.AllocateSearch.signature,leaf,saved,atCode,
      List.replicate_succ,List.replicate_zero,List.map_cons,List.map_nil,ValType.default,List.append_nil,List.length_nil,List.length_cons,arrays,leafFrame,op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  have cost : cfg.regularOpCost+(15*cfg.regularOpCost+(262*op+rest))=278*cfg.regularOpCost+rest := by dsimp [op]; omega
  simpa only [Nat.add_assoc,Nat.reduceAdd,cost] using result
end
end WNear.Proofs.AllocateFlagged
