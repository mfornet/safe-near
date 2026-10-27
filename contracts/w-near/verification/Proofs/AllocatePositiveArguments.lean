import Proofs.AllocatePositiveState

/-! Actual seven-opcode argument construction for the first580 attempt. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (h4 : frame.locals[4]?=some (.i32 (words p))) (h2 : frame.locals[2]?=some (.i32 1))
    (h3 : frame.locals[3]?=some (.i32 (scratch p))) (hc : s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (base++[Value.i32 (words p),.i32 1,.i32 (scratch p+12),.i32 1057464,.i32 1057464]).toArray frame callers (.call 580::code))) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Allocate.attempt++code)))
      (7*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have pushes : (((((base.toArray.push (.i32 (words p))).push (.i32 1)).push (.i32 (scratch p+12))).push (.i32 1057464)).push (.i32 1057464))=
      (base++[Value.i32 (words p),.i32 1,.i32 (scratch p+12),.i32 1057464,.i32 1057464]).toArray := by apply Array.toList_inj.mp; simp
  unfold WNear.Binary.Allocate.attempt
  rw [show 7*cfg.regularOpCost+rest=cfg.regularOpCost+(6*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+6) _ s limits base.toArray frame callers _ 4 (.i32 (words p)) post h4 (hc.mono (by dsimp [op]; omega))
  rw [show 6*op+rest=cfg.regularOpCost+(5*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+5) _ (paid s op 1) limits _ frame callers _ 2 (.i32 1) post h2
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5*op+rest=cfg.regularOpCost+(4*op+rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel+4) _ (paid s op 2) limits _ frame callers _ 3 (.i32 (scratch p)) post h3
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4*op+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+3) _ (paid s op 3) limits _ frame callers _ 12 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op]; omega]
  apply wp_i32_add cfg (fuel+2) _ (paid s op 4) limits ((base.toArray.push (.i32 (words p))).push (.i32 1)) frame callers _ (scratch p) 12 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel+1) _ (paid s op 5) limits _ frame callers _ 1057464 post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_const cfg fuel rest (paid s op 6) limits _ frame callers _ 1057464 post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [paid,op,pushes,List.append_eq,List.cons_append,List.nil_append] using hnext
end WNear.Proofs.AllocatePositive
