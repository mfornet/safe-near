import Proofs.AllocateRetryEmpty

/-! Actual second580 call and result assignment, using the derived fresh heap. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode AllocateFlagged.callAfter

def secondFrom (s : Store NearState) (op : Nat) (p : Layout) :=
  paid (AllocateFlagged.callAfter (paid s op 7) op (secondLayout p)) op 1
def secondFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 1 (.i32 (result p))}

theorem wp_second_attempt (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p)
    (h4 : frame.locals[4]?=some (.i32 (words p))) (h2 : frame.locals[2]?=some (.i32 1))
    (h3 : frame.locals[3]?=some (.i32 (scratch p)))
    (hcode : AllocateSearch.SearchCode s (secondLayout p) frame.inst)
    (hmem : s.mems[p.memoryIndex]?=some (secondLayout p).memory)
    (hi : p.mi.funcAddrs[580]?=some p.searchAddress)
    (hf : s.funcs[p.searchAddress]?=some (.wasm WNear.Binary.AllocateSearch.signature frame.inst WNear.Binary.Allocate.searchFunction))
    (hd : callers.length+2<limits.maxCallDepth) (hc : s.host.gas.Credits (286*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (secondFrom s cfg.regularOpCost p) limits base.toArray (secondFrame frame p) callers code)) rest post) :
    WP cfg (fuel+248) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateRetry.secondAttempt++code)))
      (286*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let active := AllocateFlagged.callAfter (paid s op 7) op (secondLayout p)
  have c7 := paid_credits s op 7 (278*op+(op+rest)) (hc.mono (by dsimp [op];omega))
  have ca := AllocateFlagged.callAfter_credits (paid s op 7) op (op+rest) (secondLayout p) c7
  have setNext : WP cfg fuel (.next (atCode (chargedStore active op) limits base.toArray
      {frame with locals:=frame.locals.set! 1 (.i32 (result p))} callers code)) rest post := by
    simpa only [secondFrom,secondFrame,paid,op,active] using hnext
  have set := wp_local_set cfg fuel rest active limits base.toArray frame callers code 1 (.i32 (result p)) post ca setNext
  have arr : (base++[Value.i32 (result p)]).toArray=base.toArray.push (.i32 (result p)) := by apply Array.toList_inj.mp;simp
  have next : WP cfg (fuel+1) (.next (atCode active limits (base++[Value.i32 (result p)]).toArray frame callers (.local_set 1::code))) (op+rest) post := by rw [arr];exact set
  have code7 : AllocateSearch.SearchCode (paid s op 7) (secondLayout p) frame.inst := by
    constructor
    · exact hcode.toCode.paid s op 7 (secondLayout p) frame.inst
    · exact hcode.sizeIndex
    · simpa only [paid,chargedStore] using hcode.sizeFunction
  have mf7 : (paid s op 7).funcs[p.searchAddress]?=some (.wasm WNear.Binary.AllocateSearch.signature frame.inst WNear.Binary.Allocate.searchFunction) := by simpa only [paid,chargedStore] using hf
  have mem7 : (paid s op 7).mems[p.memoryIndex]?=some (secondLayout p).memory := by simpa only [paid,chargedStore] using hmem
  have call := AllocateFlagged.wp_call cfg (fuel+1) (op+rest) (paid s op 7) limits base frame callers (.local_set 1::code)
    (secondLayout p) p.searchAddress post hn.second code7 mem7 hi mf7 hd c7 next
  have args := AllocatePositive.wp_arguments cfg ((fuel+1)+240) (278*op+(op+rest)) s limits base frame callers (.local_set 1::code) p.toLayout post
    h4 h2 h3 (hc.mono (by dsimp [op];omega)) call
  have cost : 7*cfg.regularOpCost+(278*op+(op+rest))=286*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateRetry.secondAttempt,List.append_assoc,List.append_eq,List.cons_append,List.nil_append,cost,Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.AllocateRetry
