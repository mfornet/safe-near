import Proofs.AllocateFlaggedFit
import Proofs.AllocateSearchMinimum

/-! Actual minimum-block-size call after the five successful split guards. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

/-- The split length is computed from the original free header. Its Native
interval derives the accepted574 path, which is then actually executed. -/
theorem wp_minimum_fit (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s p frame.inst)
    (h2 : frame.locals[2]? = some (.i32 (Allocate.splitLength p.memory (head p) p.words)))
    (hd : callers.length+1 < limits.maxCallDepth) (hc : s.host.gas.Credits (18*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (minimumFrom s cfg.regularOpCost) limits stack frame callers code)) rest post) :
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers ([.local_get 2,.call 574]++code)))
      (18*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let value := Allocate.splitLength p.memory (head p) p.words
  have number := (Allocate.split_header_numbers p.memory (head p) p.words hn.split).2.2.1
  have minimum : 8 ≤ value.toNat := by dsimp only [value]; omega
  have c1 := paid_credits s op 1 (17*op+rest) (hc.mono (by dsimp [op]; omega))
  have code1 := hcode.paid s op 1 p frame.inst
  have next : WP cfg fuel (.next (atCode (AllocateUnits.minimumAfter (paid s op 1) op) limits stack.toList.toArray frame callers code)) rest post := by
    simpa only [minimumFrom,op,Array.toArray_toList] using hnext
  have call := AllocateUnits.wp_minimum_call cfg fuel rest (paid s op 1) limits stack.toList frame callers code value p.mi p.minimumAddress post
    code1.module code1.minimumIndex code1.minimumFunction minimum hd c1 next
  have array : (stack.toList++[Value.i32 value]).toArray = stack.push (.i32 value) := by apply Array.toList_inj.mp; simp
  have callNext : WP cfg (fuel+9) (.next (atCode (paid s op 1) limits (stack.push (.i32 value)) frame callers (.call 574::code)))
      (17*op+rest) post := by simpa only [array] using call
  have result := wp_local_get cfg (fuel+9) (17*op+rest) s limits stack frame callers (.call 574::code) 2 (.i32 value) post h2
    (hc.mono (by dsimp [op]; omega)) callNext
  have cost : cfg.regularOpCost+(17*op+rest)=18*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append] using result
end WNear.Proofs.AllocateFlagged
