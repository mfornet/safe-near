import Proofs.StateDecodeRawLayout
import Proofs.AllocateVectorArguments
import Proofs.InterfaceStack

/-! Actual f767 stack reservation and complete installed f752/f751 layout call. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
def laidOutRaw (s : Store NearState) (op : Nat) (p : Layout) :=
  AllocateLayoutWrapper.called (layoutArgumentsRaw s op p) op (layout752 p)
attribute [local irreducible] WP atCode laidOutRaw
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem global_funcs (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).funcs=s.funcs:=rfl


theorem wp_raw_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (address581 address236 : Nat) (hcode : Code s frame.inst p address581 address236)
    (h1 : frame.locals[1]?=some (.i32 p.size)) (hs : 6≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.globalRaw)
    (hv : p.globalRaw.value=.i32 p.spRaw) (hd : callers.length+2<limits.maxCallDepth)
    (hc : s.host.gas.Credits (87*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (laidOutRaw s cfg.regularOpCost p) limits base.toArray
      (reservedRawFrame frame p) callers code)) rest post) :
    WP cfg (fuel+70) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodeRaw.setup 3 32++WNear.Binary.StateDecodeRaw.layoutArguments++code)))
      (87*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedRawFrame frame p
  let q := layout752 p
  have h3 : rf.locals[3]?=some (.i32 (scratch p)) := by simp [rf,reservedRawFrame,show 3<frame.locals.size by omega]
  have h1r : rf.locals[1]?=some (.i32 p.size) := by simp [rf,reservedRawFrame,h1]
  have orig := hcode.record.allocation
  have ready : AllocateLayoutWrapper.Ready (layoutArgumentsRaw s op p)
      (AllocateLayoutWrapper.leafFrame rf.inst base.length q) q := by
    exact layout_ready s op frame.inst base.length p address581 address236 hn hcode hm hg
  have arr : (base++[Value.i32 q.out,.i32 q.size]).toArray=(base.toArray.push (.i32 q.out)).push (.i32 q.size) := by
    apply Array.toList_inj.mp;simp
  have cn : WP cfg fuel (.next (atCode (AllocateLayoutWrapper.called (layoutArgumentsRaw s op p) op q) limits base.toArray rf callers code)) rest post := by
    simpa only [laidOutRaw,rf,q,op] using hnext
  have func : (layoutArgumentsRaw s op p).funcs[p.address752]?=some
      (.wasm WNear.Binary.AllocateLayout.signature rf.inst (WNear.Binary.AllocateLayout.wrapper q.calleeIndex)) := by
    simp only [layoutArgumentsRaw,reservedRaw,paid_funcs,global_funcs]
    exact hcode.function752
  have call := AllocateLayoutWrapper.wp_call cfg fuel rest (layoutArgumentsRaw s op p) limits base rf callers code q 752 p.address752 post ready
    hcode.index752 func hd (paid_credits s op 9 _ (hc.mono (by dsimp [op];omega))) cn
  rw [arr] at call
  have an : WP cfg (fuel+61) (.next (atCode (paid (reservedRaw s op p) op 4) limits
      ((base.toArray.push (.i32 (scratch p+24))).push (.i32 p.size)) rf callers (.call 752::code))) (78*op+rest) post := by
    simpa only [layoutArgumentsRaw,q,layout752,op] using call
  have args := AllocateVector.wp_layout_arguments cfg (fuel+61) (78*op+rest) (reservedRaw s op p) limits base.toArray rf callers
    (.call 752::code) (scratch p) p.size post h3 h1r
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) an
  have rn : WP cfg ((fuel+61)+4) (.next (atCode (setGlobal (paid s op 5) p.globalIndex (.i32 (p.spRaw-32))) limits base.toArray
      {frame with locals:=frame.locals.set! 3 (.i32 (p.spRaw-32))} callers
      (WNear.Binary.AllocateVector.layoutArguments++(.call 752::code)))) (4*op+(78*op+rest)) post := by
    simpa only [reservedRaw,rf,reservedRawFrame,scratch,op] using args
  have reserve := InterfaceStack.wp_reserve cfg ((fuel+61)+4) (4*op+(78*op+rest)) s limits base.toArray frame callers
    (WNear.Binary.AllocateVector.layoutArguments++(.call 752::code)) p.mi p.globalIndex p.globalRaw p.spRaw 3 32 post
    orig.search.module orig.globalIndex hg hv (hc.mono (by dsimp [op];omega)) rn
  have ce : 5*cfg.regularOpCost+(4*op+(78*op+rest))=87*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at reserve
  simpa only [WNear.Binary.StateDecodeRaw.setup,WNear.Binary.StateDecodeRaw.layoutArguments,WNear.Binary.AllocateVector.layoutArguments,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using reserve
end WNear.Proofs.StateDecodeRaw
