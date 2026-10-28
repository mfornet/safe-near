import Proofs.AllocateVectorArguments
import Proofs.AllocateVectorCode
import Proofs.InterfaceStack

/-! Actual686 reserves32 stack bytes and executes the installed685/684 layout pair. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode laidOut

theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h1 : frame.locals[1]?=some (.i32 p.size)) (hs : 6≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.outerGlobal)
    (hv : p.outerGlobal.value=.i32 p.outerSP) (hd : callers.length+2<limits.maxCallDepth)
    (hc : s.host.gas.Credits (87*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (laidOut s cfg.regularOpCost p) limits base.toArray
      (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+70) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.AllocateVector.reserve++WNear.Binary.AllocateVector.layoutArguments++[.call 685]++code)))
      (87*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedFrame frame p
  let q := layout685 p
  have h3 : rf.locals[3]?=some (.i32 (reservedSP p)) := by simp [rf,reservedFrame,show 3<frame.locals.size by omega]
  have h1r : rf.locals[1]?=some (.i32 p.size) := by simp [rf,reservedFrame,h1]
  have orig := hcode.allocation.allocation.retry.originalCode
  have ag : (arguments s op p).globals[p.globalIndex]?=some q.global := by
    simp only [arguments,reserved,paid,chargedStore,setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true,q,layout685]
  have bounds := setup_bounds p hn
  have om : s.modules[frame.inst]?=some p.mi := by
    simpa only [AllocatePositive.searchLayout] using orig.search.module
  have am : (arguments s op p).modules[(AllocateLayoutWrapper.leafFrame rf.inst base.length q).inst]?=some q.mi := by
    simpa only [arguments,reserved,paid,chargedStore,setGlobal,AllocateLayoutWrapper.leafFrame,rf,reservedFrame,q,layout685] using om
  have af : (arguments s op p).funcs[p.address684]?=some (.wasm WNear.Binary.AllocateLayout.signature
      (AllocateLayoutWrapper.leafFrame rf.inst base.length q).inst
      (WNear.Binary.AllocateLayout.function q.message q.location q.previous)) := by
    simpa only [q,layout685,WNear.Binary.AllocateLayout.function684,arguments,reserved,paid,chargedStore,setGlobal,rf,reservedFrame,AllocateLayoutWrapper.leafFrame] using hcode.function684
  have ame : (arguments s op p).mems[q.memoryIndex]?=some q.memory := by
    simpa only [arguments,reserved,paid,chargedStore,setGlobal,q,layout685] using hm
  have ready : AllocateLayoutWrapper.Ready (arguments s op p)
      (AllocateLayoutWrapper.leafFrame rf.inst base.length q) q := by
    refine ⟨am,orig.globalIndex,ag,rfl,orig.search.memoryIndex,ame,hcode.index684,af,rfl,rfl,?_,
      hn.allocation.wf,hn.allocation.width,bounds.1,bounds.2⟩
    simp only [AllocateLayoutWrapper.leafFrame,List.size_toArray,List.length_cons,List.length_nil]
    decide
  have arr : (base++[Value.i32 q.out,.i32 q.size]).toArray=(base.toArray.push (.i32 q.out)).push (.i32 q.size) := by
    apply Array.toList_inj.mp;simp
  have cn : WP cfg fuel (.next (atCode (AllocateLayoutWrapper.called (arguments s op p) op q) limits base.toArray rf callers code)) rest post := by
    simpa only [laidOut,rf,q,op] using hnext
  have call := AllocateLayoutWrapper.wp_call cfg fuel rest (arguments s op p) limits base rf callers code q 685 p.address685 post ready
    hcode.index685 (by simpa only [q,layout685,arguments,reserved,paid,chargedStore,setGlobal,rf,reservedFrame,WNear.Binary.AllocateLayout.function685] using hcode.function685) hd (paid_credits s op 9 _ (hc.mono (by dsimp [op];omega))) cn
  rw [arr] at call
  have an : WP cfg (fuel+61) (.next (atCode (paid (reserved s op p) op 4) limits
      ((base.toArray.push (.i32 (reservedSP p+24))).push (.i32 p.size)) rf callers (.call 685::code))) (78*op+rest) post := by
    simpa only [arguments,q,layout685,op] using call
  have args := wp_layout_arguments cfg (fuel+61) (78*op+rest) (reserved s op p) limits base.toArray rf callers
    (.call 685::code) (reservedSP p) p.size post h3 h1r
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) an
  have rn : WP cfg ((fuel+61)+4) (.next (atCode (setGlobal (paid s op 5) p.globalIndex (.i32 (p.outerSP-32))) limits base.toArray
      {frame with locals:=frame.locals.set! 3 (.i32 (p.outerSP-32))} callers
      (WNear.Binary.AllocateVector.layoutArguments++(.call 685::code)))) (4*op+(78*op+rest)) post := by
    simpa only [reserved,rf,reservedFrame,reservedSP,op] using args
  have reserve := InterfaceStack.wp_reserve cfg ((fuel+61)+4) (4*op+(78*op+rest)) s limits base.toArray frame callers
    (WNear.Binary.AllocateVector.layoutArguments++(.call 685::code)) p.mi p.globalIndex p.outerGlobal p.outerSP 3 32 post
    orig.search.module orig.globalIndex hg hv (hc.mono (by dsimp [op];omega)) rn
  have ce : 5*cfg.regularOpCost+(4*op+(78*op+rest))=87*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at reserve
  simpa only [WNear.Binary.AllocateVector.reserve,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using reserve
end WNear.Proofs.AllocateVector
