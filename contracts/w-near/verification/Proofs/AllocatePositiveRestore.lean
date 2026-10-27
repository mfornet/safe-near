import Proofs.AllocatePositiveState

/-! Actual final SP restoration and result local of581. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def restoreFrom (s : Store NearState) (op index : Nat) (sp : UInt32) := paid (setGlobal (paid s op 4) index (.i32 sp)) op 1

theorem wp_restore_result (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (global : GlobalInst) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 (scratch p))) (h1 : frame.locals[1]?=some (.i32 (result p)))
    (hm : s.modules[frame.inst]?=some p.mi) (hi : p.mi.globalAddrs[0]?=some p.globalIndex)
    (hg : s.globals[p.globalIndex]?=some global) (hs : scratch p+16=p.sp)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (restoreFrom s cfg.regularOpCost p.globalIndex p.sp) limits
      (stack.push (.i32 (result p))) frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.AllocatePositive.restore++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let restored := setGlobal (paid s op 4) p.globalIndex (.i32 p.sp)
  have c4 : restored.host.gas.Credits (op+rest) := paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  have next : WP cfg fuel (.next (atCode (chargedStore restored cfg.regularOpCost) limits
      (stack.push (.i32 (result p))) frame callers code)) rest post := by simpa only [restoreFrom,restored,paid,op] using hnext
  have get := wp_local_get cfg fuel rest restored limits stack frame callers code 1 (.i32 (result p)) post h1 c4 next
  have restoreNext : WP cfg (fuel+1) (.next (atCode (setGlobal (paid s cfg.regularOpCost 4) p.globalIndex (.i32 (scratch p+16))) limits stack
      frame callers (.local_get 1::code))) (op+rest) post := by simpa only [restored,hs,op] using get
  have restore := ValueReturnBorrow.wp_restore cfg (fuel+1) (op+rest) s limits stack frame callers (.local_get 1::code)
    p.mi p.globalIndex global (scratch p) 3 post h3 hm hi hg (hc.mono (by dsimp [op]; omega)) restoreNext
  have cost : 4*cfg.regularOpCost+(op+rest)=5*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at restore
  simpa only [WNear.Binary.AllocatePositive.restore,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using restore
end WNear.Proofs.AllocatePositive
