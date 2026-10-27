import Binary.AllocateLoop
import Proofs.AllocateSearchPhases

/-! The actual572 call computes the candidate's byte count. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode AllocateUnits.unitsAfter

def unitsFrom (s : Store NearState) (op : Nat) := paid (AllocateUnits.unitsAfter (paid s op 1) op) op 1
def unitsFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 10 (.i32 (p.words*4))}

theorem shift_two (value : UInt32) : value <<< (2 : UInt32) = value * 4 := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_shiftLeft,UInt32.toNat_mul,Nat.shiftLeft_eq]

theorem wp_candidate_units (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s p frame.inst)
    (hw : frame.locals[0]? = some (.i32 p.words)) (hd : callers.length+1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (21*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (unitsFrom s cfg.regularOpCost) limits stack (unitsFrame frame p) callers code)) rest post) :
    WP cfg (fuel+14) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateSearch.candidateUnits++code)))
      (21*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have room := hn.split.room
  have endLt := UInt32.toNat_lt (Allocate.endWord p.memory (head p))
  have wordBound : p.words.toNat < 2^30 := by omega
  have c1 := paid_credits s op 1 (19*op+(op+rest)) (hc.mono (by dsimp [op]; omega))
  have c20 := AllocateUnits.unitsAfter_credits (paid s op 1) op (op+rest) c1
  have next : WP cfg fuel (.next (atCode (chargedStore (AllocateUnits.unitsAfter (paid s op 1) op) cfg.regularOpCost)
      limits stack (unitsFrame frame p) callers code)) rest post := by simpa only [unitsFrom,paid,op] using hnext
  have set := wp_local_set cfg fuel rest (AllocateUnits.unitsAfter (paid s op 1) op) limits stack frame callers code
    10 (.i32 (p.words*4)) post c20 next
  have arr : (stack.toList++[Value.i32 (p.words*4)]).toArray = stack.push (.i32 (p.words*4)) := by apply Array.toList_inj.mp; simp
  have callNext : WP cfg (fuel+1) (.next (atCode (AllocateUnits.unitsAfter (paid s op 1) op) limits
      (stack.toList++[Value.i32 (p.words <<< (2:UInt32))]).toArray frame callers (.local_set 10::code))) (op+rest) post := by
    simpa only [shift_two,arr,unitsFrame] using set
  have c := hcode.paid s op 1 p frame.inst
  have call := AllocateUnits.wp_units_call cfg (fuel+1) (op+rest) (paid s op 1) limits stack.toList frame callers
    (.local_set 10::code) p.words p.mi p.unitsAddress post c.module c.unitsIndex c.unitsFunction wordBound hd c1 callNext
  have arg : (stack.toList++[Value.i32 p.words]).toArray = stack.push (.i32 p.words) := by apply Array.toList_inj.mp; simp
  have getNext : WP cfg (fuel+13) (.next (atCode (paid s op 1) limits (stack.push (.i32 p.words)) frame callers
      (.call 572::.local_set 10::code))) (20*op+rest) post := by
    have cost : 19*cfg.regularOpCost+(op+rest)=20*op+rest := by dsimp [op]; omega
    rw [cost] at call
    simpa only [arg,Nat.add_assoc,Nat.reduceAdd] using call
  have result := wp_local_get cfg (fuel+13) (20*op+rest) s limits stack frame callers _ 0 (.i32 p.words) post hw
    (hc.mono (by dsimp [op]; omega)) getNext
  have cost : cfg.regularOpCost+(20*op+rest)=21*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [WNear.Binary.AllocateSearch.candidateUnits,List.append_eq,List.cons_append,List.nil_append] using result
end WNear.Proofs.AllocateSearch
