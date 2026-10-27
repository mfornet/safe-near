import Proofs.AllocateEmptyBody
import Proofs.AllocateSearchCall

/-! Typed empty-list580 call with exact gas and unchanged linear memories. -/
namespace WNear.Proofs.AllocateEmpty
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout head initialFrame entered entered_credits leafFrame)
open StorePairCaller (paid paid_credits)
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode after

def callAfter (s : Store NearState) (op : Nat) := after (entered s op) op

theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (address : Nat) (post : Post)
    (hh : head p=0) (hm : s.modules[frame.inst]?=some p.mi)
    (hmi : p.mi.memAddrs[0]?=some p.memoryIndex) (hb : p.root.toNat+4≤p.memory.byteSize)
    (hmem : s.mems[p.memoryIndex]?=some p.memory)
    (hi : p.mi.funcAddrs[580]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.AllocateSearch.signature frame.inst WNear.Binary.Allocate.searchFunction))
    (hd : callers.length+2<limits.maxCallDepth) (hc : s.host.gas.Credits (37*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost) limits
      (base++[Value.i32 0]).toArray frame callers code)) rest post) :
    WP cfg (fuel+25) (.next (atCode s limits (base++[Value.i32 p.words,.i32 1,.i32 p.root,.i32 p.context,.i32 p.vtable]).toArray
      frame callers (.call 580::code))) (37*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have ca := entered_credits s op (21*op+rest) (hc.mono (by dsimp [op]; omega))
  have cf : (callAfter s op).host.gas.Credits rest := by
    simpa only [callAfter,after,active] using paid_credits active op 21 rest ca
  have sh : (initialFrame leaf p).arity=leaf.arity ∧ (initialFrame leaf p).height=leaf.height ∧
      (initialFrame leaf p).labels=leaf.labels := ⟨rfl,rfl,rfl⟩
  have arity : [Value.i32 0].length=(initialFrame leaf p).arity := by rw [sh.1]; rfl
  have height : (initialFrame leaf p).height=base.length := by rw [sh.2.1]; rfl
  have labels : (initialFrame leaf p).labels=[] := by rw [sh.2.2]; rfl
  have leaveNext : WP cfg fuel (.next (atCode (callAfter s op) limits (base++[Value.i32 0]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have leave := wp_leave_wasm cfg fuel rest (callAfter s op) limits base [.i32 0] (initialFrame leaf p) saved callers post arity height labels cf leaveNext
  have arr : (base++[Value.i32 0]).toArray=base.toArray.push (.i32 0) := by apply Array.toList_inj.mp; simp
  have bn : WP cfg (fuel+1) (.next (atCode (after active op) limits (base.toArray.push (.i32 0))
      (initialFrame leaf p) (saved::callers) [])) rest post := by simpa only [callAfter,active,arr] using leave
  have memActive : active.mems[p.memoryIndex]?=some p.memory := hmem
  have body := wp_body cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] p post rfl rfl (by simp [leaf,leafFrame]) hh hm hmi memActive hb ca bn
  have callRule := wp_call_wasm cfg ((fuel+1)+23) (21*op+rest) s limits base
    [.i32 p.words,.i32 1,.i32 p.root,.i32 p.context,.i32 p.vtable] frame callers code 580 address p.mi
    WNear.Binary.AllocateSearch.signature frame.inst WNear.Binary.Allocate.searchFunction post hm hi hf rfl (by omega)
  rw [WNear.Binary.AllocateSearch.activation] at callRule
  have arrays : #[Value.i32 p.words,Value.i32 1,Value.i32 p.root,Value.i32 p.context,Value.i32 p.vtable]++
      #[Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0,Value.i32 0]=
      (leafFrame frame.inst base.length p).locals := by apply Array.toList_inj.mp; simp [leafFrame]
  have next : WP cfg ((fuel+1)+23) (.next (wasmCallee active limits base frame callers code WNear.Binary.AllocateSearch.signature
      frame.inst WNear.Binary.Allocate.searchFunction [.i32 p.words,.i32 1,.i32 p.root,.i32 p.context,.i32 p.vtable])) (21*op+rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateSearch.function_locals,WNear.Binary.AllocateSearch.signature,leaf,saved,atCode,
      List.replicate_succ,List.replicate_zero,List.map_cons,List.map_nil,ValType.default,List.append_nil,List.length_nil,List.length_cons,arrays,leafFrame,op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  have cost : cfg.regularOpCost+(15*cfg.regularOpCost+(21*op+rest))=37*cfg.regularOpCost+rest := by dsimp [op]; omega
  simpa only [Nat.add_assoc,Nat.reduceAdd,cost] using result
end
end WNear.Proofs.AllocateEmpty
