import Binary.StateDecodeScalar
import Proofs.StorePairCallerState
import NearVM.MeteredI32MemoryRules
import NearVM.MeteredNumericRules
import NearVM.MeteredLoopRules

/-! Accepted scalar length and status checks execute their deployed guest instructions. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32

def lengthFrame (frame : CallFrame) (memory : Memory) (slice : UInt32) :=
  {frame with locals:=frame.locals.set! 3 (.i32 (readI32 memory (slice.toNat+4)))}
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_length_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (slice : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hb : slice.toNat+4+4≤memory.byteSize)
    (hn : (WNear.Binary.StateDecodeScalar.width wide).toNat≤(readI32 memory (slice.toNat+4)).toNat)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack (lengthFrame frame memory slice) callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      (.block .empty (WNear.Binary.StateDecodeScalar.lengthGuard wide++WNear.Binary.StateDecodeScalar.tooShort)::code)))
      (6*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let len := readI32 memory (slice.toNat+4)
  let threshold := WNear.Binary.StateDecodeScalar.width wide-1
  let lf := lengthFrame frame memory slice
  let bf := emptyBlockFrame frame stack.size code
  let nf := emptyBlockFrame lf stack.size code
  have gt : threshold<len := by
    change threshold.toNat<len.toNat
    cases wide <;> simp only [threshold,WNear.Binary.StateDecodeScalar.width,Bool.false_eq_true,ite_false,ite_true] at hn ⊢ <;> exact (by dsimp [len] at *;omega)
  have test : Numeric.bool (Numeric.irelop32 .gt_u len threshold)≠0 := by simp [Numeric.irelop32,Numeric.bool,gt]
  have br := wp_br_if_block_nonzero cfg fuel rest (paid s op 5) limits stack lf callers code WNear.Binary.StateDecodeScalar.tooShort
    (Numeric.bool (Numeric.irelop32 .gt_u len threshold)) post test (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) hnext
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 4) limits stack nf callers
    (.br_if 0::WNear.Binary.StateDecodeScalar.tooShort) .gt_u len threshold post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) br
  have con := wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits (stack.push (.i32 len)) nf callers
    (.i32_relop .gt_u::.br_if 0::WNear.Binary.StateDecodeScalar.tooShort) threshold post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) rel
  have tee := wp_local_tee cfg (fuel+3) (op+(op+(op+rest))) (paid s op 2) limits stack bf callers
    (.i32_const threshold::.i32_relop .gt_u::.br_if 0::WNear.Binary.StateDecodeScalar.tooShort) 3 (.i32 len) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) con
  have mm : (paid s op 1).modules[bf.inst]?=some mi := by rw [modules_paid];exact hm
  have me : (paid s op 1).mems[index]?=some memory := by rw [mems_paid];exact he
  have load := wp_i32_load cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 1) limits stack bf callers
    (.local_tee 3::.i32_const threshold::.i32_relop .gt_u::.br_if 0::WNear.Binary.StateDecodeScalar.tooShort) {align:=2,offset:=4} slice mi index memory post
    mm hi me hb (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) tee
  have get := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) s limits stack bf callers
    (.load .i32 none {align:=2,offset:=4}::.local_tee 3::.i32_const threshold::.i32_relop .gt_u::.br_if 0::WNear.Binary.StateDecodeScalar.tooShort) 1 (.i32 slice) post h1
    (hc.mono (by dsimp [op];omega)) load
  have inside : WP cfg (fuel+6) (.next (atCode s limits stack bf callers
      (WNear.Binary.StateDecodeScalar.lengthGuard wide++WNear.Binary.StateDecodeScalar.tooShort))) (6*cfg.regularOpCost+rest) post := by
    simpa only [WNear.Binary.StateDecodeScalar.lengthGuard,threshold,List.cons_append,List.nil_append,
      show cfg.regularOpCost+(op+(op+(op+(op+(op+rest)))))=6*cfg.regularOpCost+rest by dsimp [op];omega] using get
  exact wp_block_empty cfg (fuel+6) _ s limits stack frame callers _ code post hc inside
end WNear.Proofs.StateDecodeScalar
