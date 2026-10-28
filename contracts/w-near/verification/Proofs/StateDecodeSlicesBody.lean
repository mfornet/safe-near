import Proofs.StateDecodeSlicesWrites

/-! Complete accepted deployed361/362 bodies; no panic callee is invoked. -/
namespace WNear.Proofs.StateDecodeSlices
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def after (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32) :=
  writesAfter drop (paid s op 4) op index memory out pointer len split

theorem after_credits (drop : Bool) (s : Store NearState) (op index rest : Nat)
    (memory : Memory) (out pointer len split : UInt32)
    (hc : s.host.gas.Credits (WNear.Binary.StateDecodeSlices.bodyCost drop*op+rest)) :
    (after drop s op index memory out pointer len split).host.gas.Credits rest := by
  cases drop with
  | false =>
    simpa only [after,writesAfter,highStore,wordCount,storeI32_host,Bool.false_eq_true,ite_false,paid,chargedStore] using
      paid_credits s op 10 rest hc
  | true =>
    simpa only [after,writesAfter,highStore,wordCount,storeI32_host,ite_true,paid,chargedStore] using
      paid_credits s op 14 rest hc

private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (drop : Bool) (out pointer len split : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h1 : frame.locals[1]?=some (.i32 pointer))
    (h2 : frame.locals[2]?=some (.i32 len)) (h3 : frame.locals[3]?=some (.i32 split))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hwf : memory.wf) (hb : out.toNat+8≤memory.byteSize) (hn : split.toNat≤len.toNat)
    (hc : s.host.gas.Credits (WNear.Binary.StateDecodeSlices.bodyCost drop*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after drop s cfg.regularOpCost index memory out pointer len split)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel+WNear.Binary.StateDecodeSlices.bodySteps drop) (.next (atCode s limits stack frame callers
      (WNear.Binary.StateDecodeSlices.body drop++code)))
      (WNear.Binary.StateDecodeSlices.bodyCost drop*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let gs := paid s op 4
  have cut : 4*op+(2*wordCount drop)*op+rest=WNear.Binary.StateDecodeSlices.bodyCost drop*op+rest := by
    cases drop <;> simp [wordCount,WNear.Binary.StateDecodeSlices.bodyCost] <;> omega
  have cg := paid_credits s op 4 ((2*wordCount drop)*op+rest) (hc.mono (by rw [←cut];omega))
  have gm : gs.modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have ge : gs.mems[index]?=some memory := by rw [mems_paid];exact he
  have writes := wp_writes cfg fuel rest gs limits stack frame callers code drop out pointer len split mi index memory post
    h0 h1 h2 h3 gm hi ge hwf hb cg hnext
  have guard := wp_guard cfg (fuel+2*wordCount drop) ((2*wordCount drop)*op+rest) s limits stack frame callers
    ((if drop then WNear.Binary.StateDecodeSlices.dropWrites else WNear.Binary.StateDecodeSlices.takeWrites)++code)
    drop len split post h2 h3 hn (hc.mono (by rw [←cut];omega)) writes
  have ce : 4*cfg.regularOpCost+((2*wordCount drop)*op+rest)=WNear.Binary.StateDecodeSlices.bodyCost drop*cfg.regularOpCost+rest := by
    dsimp [op] at cut ⊢;omega
  have fe : (fuel+2*wordCount drop)+5=fuel+WNear.Binary.StateDecodeSlices.bodySteps drop := by
    cases drop <;> simp [wordCount,WNear.Binary.StateDecodeSlices.bodySteps,WNear.Binary.StateDecodeSlices.bodyCost]
  rw [ce,fe] at guard
  simpa only [WNear.Binary.StateDecodeSlices.body,List.cons_append,List.nil_append] using guard
end WNear.Proofs.StateDecodeSlices
