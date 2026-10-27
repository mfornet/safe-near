import Proofs.AllocatePositiveBody

/-! Typed actual581 call for the positive-size, directly-fitting search branch. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
attribute [local irreducible] WP atCode after

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def callAfter (s : Store NearState) (op : Nat) (p : Layout) := after (entered s op) op p
def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.allocator,.i32 p.size,.i32 1,.i32 0,.i32 0],inst,arity:=1,height,labels:=[],code:=[]}

theorem entered_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (12*op+rest)) :
    (entered s op).host.gas.Credits rest := by
  have a := StorePair.charged_credits s op (11*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (11*op) rest a

theorem callAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (358*op+rest)) :
    (callAfter s op p).host.gas.Credits rest := by
  unfold callAfter
  exact after_credits _ op rest p (entered_credits s op _ (hc.mono (by omega)))

theorem resultFrame_shape (frame : CallFrame) (p : Layout) :
    (resultFrame frame p).arity=frame.arity ∧ (resultFrame frame p).height=frame.height ∧ (resultFrame frame p).labels=frame.labels := by
  simp only [resultFrame,prefixFrame,reservedFrame,Allocate.roundedFrame,and_self]

/-- Actual typed581 entry, the full297-step positive body, and normal pointer
return, including original SP restoration and the sequential allocator write. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p)
    (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hglobal : s.globals[p.globalIndex]?=some p.global) (hsp : p.global.value=.i32 p.sp)
    (hi : p.mi.funcAddrs[581]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.Allocate.signature frame.inst WNear.Binary.Allocate.function))
    (hd : callers.length+3<limits.maxCallDepth) (hc : s.host.gas.Credits (358*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost p) limits
      (base++[Value.i32 (result p)]).toArray frame callers code)) rest post) :
    WP cfg (fuel+299) (.next (atCode s limits (base++[Value.i32 p.allocator,.i32 p.size,.i32 1]).toArray
      frame callers (.call 581::code))) (358*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ca := entered_credits s op (346*op+rest) (hc.mono (by dsimp [op]; omega))
  have cf := callAfter_credits s op rest p hc
  have shape := resultFrame_shape leaf p
  have arity : [Value.i32 (result p)].length=(resultFrame leaf p).arity := by rw [shape.1]; rfl
  have height : (resultFrame leaf p).height=base.length := by rw [shape.2.1]; rfl
  have labels : (resultFrame leaf p).labels=[] := by rw [shape.2.2]; rfl
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op p) limits (base++[Value.i32 (result p)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter s op p) limits base [.i32 (result p)] (resultFrame leaf p) saved callers post arity height labels cf leaveNext
  have arr : (base++[Value.i32 (result p)]).toArray=base.toArray.push (.i32 (result p)) := by apply Array.toList_inj.mp; simp
  have bn : WP cfg (fuel+1) (.next (atCode (after active op p) limits (base.toArray.push (.i32 (result p))) (resultFrame leaf p)
      (saved::callers) [])) rest post := by simpa only [callAfter,active,arr] using leave
  have codeActive : Code active leaf.inst p := hcode.transport s active frame.inst p rfl rfl rfl
  have memActive : active.mems[p.memoryIndex]?=some p.memory := hmem
  have globalActive : active.globals[p.globalIndex]?=some p.global := hglobal
  have body := wp_body cfg (fuel+1) rest active limits base leaf (saved::callers) [] p post hn codeActive
    rfl rfl rfl (by simp [leaf,leafFrame]) memActive globalActive hsp (by simpa only [List.length_cons] using hd) ca bn
  have callRule := wp_call_wasm cfg ((fuel+1)+297) (346*op+rest) s limits base [.i32 p.allocator,.i32 p.size,.i32 1]
    frame callers code 581 address p.mi WNear.Binary.Allocate.signature frame.inst WNear.Binary.Allocate.function post hcode.search.module hi hf rfl (by omega)
  have activation : activationGas op (wasmLocals WNear.Binary.Allocate.function [.i32 p.allocator,.i32 p.size,.i32 1])=11*op := by
    simp [activationGas,wasmLocals,WNear.Binary.Allocate.function,ValType.default]
  rw [activation] at callRule
  have arrays : #[Value.i32 p.allocator,Value.i32 p.size,Value.i32 1]++#[Value.i32 0,Value.i32 0]= (leafFrame frame.inst base.length p).locals := by
    apply Array.toList_inj.mp; simp [leafFrame]
  have next : WP cfg ((fuel+1)+297) (.next (wasmCallee active limits base frame callers code WNear.Binary.Allocate.signature frame.inst
      WNear.Binary.Allocate.function [.i32 p.allocator,.i32 p.size,.i32 1])) (346*op+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.Allocate.function,WNear.Binary.Allocate.signature,leaf,saved,atCode,List.map_cons,List.map_nil,
      ValType.default,List.append_nil,List.length_cons,List.length_nil,arrays,leafFrame,op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  have cost : cfg.regularOpCost+(11*op+(346*op+rest))=358*cfg.regularOpCost+rest := by dsimp [op]; omega
  simpa only [cost,Nat.add_assoc,Nat.reduceAdd] using result
end WNear.Proofs.AllocatePositive
