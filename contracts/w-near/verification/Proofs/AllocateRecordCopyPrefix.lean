import Proofs.AllocateRecordCopyState
import Proofs.ValueReturnBorrow

/-! Actual690 shadow-stack reservation and six callee argument instructions. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

private theorem wp_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p)
    (h3 : frame.locals[3]?=some (.i32 p.inner.sp)) (h1 : frame.locals[1]?=some (.i32 p.inner.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      ((((stack.push (.i32 p.inner.out)).push (.i32 p.inner.size)).push (.i32 1)).push (.i32 1)) frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateRecordCopy.arguments++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have k1 := wp_i32_const cfg fuel rest (paid s op 5) limits (((stack.push (.i32 p.inner.out)).push (.i32 p.inner.size)).push (.i32 1)) frame callers code 1 post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) hnext
  have g2 := wp_local_get cfg (fuel+1) (op+rest) (paid s op 4) limits ((stack.push (.i32 p.inner.out)).push (.i32 p.inner.size)) frame callers _ 2 (.i32 1) post h2
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) k1
  have g1 := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits (stack.push (.i32 p.inner.out)) frame callers _ 1 (.i32 p.inner.size) post h1
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) g2
  have addNext : WP cfg (fuel+3) (.next (atCode (chargedStore (paid s op 2) op) limits
      (stack.push (.i32 (p.inner.sp+8))) frame callers (.local_get 1::.local_get 2::.i32_const 1::code))) (op+(op+(op+rest))) post := by
    simpa only [←hn.innerOut,paid,op] using g1
  have add := wp_i32_add cfg (fuel+3) (op+(op+(op+rest))) (paid s op 2) limits stack frame callers _ p.inner.sp 8 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) addNext
  have k8 := wp_i32_const cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 1) limits (stack.push (.i32 p.inner.sp)) frame callers _ 8 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) add
  have get := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) s limits stack frame callers _ 3 (.i32 p.inner.sp) post h3
    (hc.mono (by dsimp [op];omega)) k8
  have ce : cfg.regularOpCost+(op+(op+(op+(op+(op+rest)))))=6*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [WNear.Binary.AllocateRecordCopy.arguments,List.cons_append,List.nil_append,ce,Nat.add_assoc,Nat.reduceAdd] using get

theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h1 : frame.locals[1]?=some (.i32 p.inner.size)) (h2 : frame.locals[2]?=some (.i32 1))
    (hs : 4≤frame.locals.size) (hg : s.globals[p.inner.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hc : s.host.gas.Credits (11*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (arguments s cfg.regularOpCost p) limits
      (base++[Value.i32 p.inner.out,.i32 p.inner.size,.i32 1,.i32 1]).toArray (resultFrame frame p) callers code)) rest post) :
    WP cfg (fuel+11) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.AllocateRecordCopy.reserve++WNear.Binary.AllocateRecordCopy.arguments++code)))
      (11*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let rf := resultFrame frame p
  have h3 : rf.locals[3]?=some (.i32 p.inner.sp) := by simp [rf,resultFrame,show 3<frame.locals.size by omega]
  have h1r : rf.locals[1]?=some (.i32 p.inner.size) := by simp [rf,resultFrame,h1]
  have h2r : rf.locals[2]?=some (.i32 1) := by simp [rf,resultFrame,h2]
  have arr : (base++[Value.i32 p.inner.out,.i32 p.inner.size,.i32 1,.i32 1]).toArray=
      ((((base.toArray.push (.i32 p.inner.out)).push (.i32 p.inner.size)).push (.i32 1)).push (.i32 1)) := by apply Array.toList_inj.mp;simp
  have next : WP cfg fuel (.next (atCode (paid (reserved s op p) op 6) limits
      ((((base.toArray.push (.i32 p.inner.out)).push (.i32 p.inner.size)).push (.i32 1)).push (.i32 1)) rf callers code)) rest post := by
    simpa only [arguments,rf,op,arr] using hnext
  have args := wp_arguments cfg fuel rest (reserved s op p) limits base.toArray rf callers code p post hn h3 h1r h2r
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) next
  have reserveNext : WP cfg (fuel+6) (.next (atCode (setGlobal (paid s op 5) p.inner.globalIndex (.i32 (p.sp-16))) limits base.toArray
      {frame with locals:=frame.locals.set! 3 (.i32 (p.sp-16))} callers (WNear.Binary.AllocateRecordCopy.arguments++code))) (6*op+rest) post := by
    simpa only [reserved,rf,resultFrame,hn.innerSP,Nat.add_assoc,Nat.reduceAdd] using args
  have reserve := ValueReturnBorrow.wp_reserve cfg (fuel+6) (6*op+rest) s limits base.toArray frame callers
    (WNear.Binary.AllocateRecordCopy.arguments++code) p.inner.mi p.inner.globalIndex p.global p.sp 3 post
    hcode.inner.allocation.retry.originalCode.search.module hcode.inner.allocation.retry.originalCode.globalIndex hg hv
    (hc.mono (by dsimp [op];omega)) reserveNext
  have ce : 5*cfg.regularOpCost+(6*op+rest)=11*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at reserve
  simpa only [WNear.Binary.AllocateRecordCopy.reserve,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using reserve
end WNear.Proofs.AllocateRecordCopy
