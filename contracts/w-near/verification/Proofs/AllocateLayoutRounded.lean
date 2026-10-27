import Binary.AllocateLayout
import NearVM.MeteredBitRules
import Proofs.StorePairCallerState
import Proofs.ValueReturnOuterBody

/-! Actual alignment-one rounded-size instruction sequence. -/
namespace WNear.Proofs.AllocateLayout
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP readI32 writeI32

theorem rounded_one (size : UInt32) : ((1 + size) + 4294967295) &&& (0 - 1) = size := by
  have add : (1 + size) + (4294967295 : UInt32) = size := by
    rw [UInt32.add_comm 1 size, UInt32.add_assoc, show (1 : UInt32) + 4294967295 = 0 by decide, UInt32.add_zero]
  rw [add]
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_and]
  change size.toBitVec &&& BitVec.allOnes 32 = size.toBitVec
  exact BitVec.and_allOnes

def roundedCode : Expr := [.local_get 0,.local_get 3,.local_get 1,.i32_binop .add,.i32_const 4294967295,
  .i32_binop .add,.i32_const 0,.local_get 3,.i32_binop .sub,.i32_binop .and,.store .i32 none {align := 2,offset := 0}]
def roundedStore (s : Store NearState) (op index : Nat) (out size : UInt32) (memory : Memory) :=
  storeI32 (paid s op 11) index out.toNat memory size

private theorem normalize {cfg : WasmConfig} {fuel : Nat} {c : StepResult NearState} {post : Post}
    (n rest : Nat) (h : WP cfg fuel c (cfg.regularOpCost + (n * cfg.regularOpCost + rest)) post) :
    WP cfg fuel c ((n + 1) * cfg.regularOpCost + rest) post := by
  rw [show (n + 1) * cfg.regularOpCost + rest = cfg.regularOpCost + (n * cfg.regularOpCost + rest) by rw [Nat.add_mul,Nat.one_mul]; omega]
  exact h

/-- The actual rounding arithmetic writes the original size for alignment one,
including wraparound sizes; no native addition-room premise is needed. -/
theorem wp_rounded (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (out size : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]? = some (.i32 out)) (hs : frame.locals[1]? = some (.i32 size))
    (ha : frame.locals[3]? = some (.i32 1))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : out.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (11 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (roundedStore s cfg.regularOpCost index out size memory) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 11) (.next (atCode s limits stack frame callers (roundedCode ++ code))) (11 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm10 : (paid s op 10).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have mm10 : (paid s op 10).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have st := wp_i32_store cfg fuel rest (paid s op 10) limits stack frame callers code {align := 2,offset := 0} out size mi index memory post hm10 hi mm10 hb
    (paid_credits s op 10 _ (hc.mono (by dsimp [op]; omega))) hnext
  let c10 := .store .i32 none {align := 2,offset := 0} :: code
  let c9 := .i32_binop .and :: c10
  let c8 := .i32_binop .sub :: c9
  let c7 := .local_get 3 :: c8
  let c6 := .i32_const 0 :: c7
  let c5 := .i32_binop .add :: c6
  let c4 := .i32_const 4294967295 :: c5
  let c3 := .i32_binop .add :: c4
  let c2 := .local_get 1 :: c3
  let c1 := .local_get 3 :: c2
  have sn : WP cfg (fuel + 1) (.next (atCode (paid s op 10) limits
      ((stack.push (.i32 out)).push (.i32 (((1 + size) + 4294967295) &&& (0 - 1)))) frame callers c10)) (1 * cfg.regularOpCost + rest) post := by
    simpa only [rounded_one, Nat.one_mul, c10] using st
  have r2 := wp_i32_and cfg (fuel + 1) (1 * op + rest) (paid s op 9) limits (stack.push (.i32 out)) frame callers c10
    ((1 + size) + 4294967295) (0 - 1) post (paid_credits s op 9 _ (hc.mono (by dsimp [op]; omega))) sn
  have p2 := normalize 1 rest r2
  have r3 := wp_i32_sub cfg (fuel + 2) (2 * op + rest) (paid s op 8) limits
    ((stack.push (.i32 out)).push (.i32 ((1 + size) + 4294967295))) frame callers c9 0 1 post
    (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) p2
  have p3 := normalize 2 rest r3
  have r4 := wp_local_get cfg (fuel + 3) (3 * op + rest) (paid s op 7) limits
    (((stack.push (.i32 out)).push (.i32 ((1 + size) + 4294967295))).push (.i32 0)) frame callers c8 3 (.i32 1) post ha
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) p3
  have p4 := normalize 3 rest r4
  have r5 := wp_i32_const cfg (fuel + 4) (4 * op + rest) (paid s op 6) limits
    ((stack.push (.i32 out)).push (.i32 ((1 + size) + 4294967295))) frame callers c7 0 post
    (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) p4
  have p5 := normalize 4 rest r5
  have r6 := wp_i32_add cfg (fuel + 5) (5 * op + rest) (paid s op 5) limits (stack.push (.i32 out)) frame callers c6
    (1 + size) 4294967295 post (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) p5
  have p6 := normalize 5 rest r6
  have r7 := wp_i32_const cfg (fuel + 6) (6 * op + rest) (paid s op 4) limits
    ((stack.push (.i32 out)).push (.i32 (1 + size))) frame callers c5 4294967295 post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) p6
  have p7 := normalize 6 rest r7
  have r8 := wp_i32_add cfg (fuel + 7) (7 * op + rest) (paid s op 3) limits (stack.push (.i32 out)) frame callers c4 1 size post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) p7
  have p8 := normalize 7 rest r8
  have r9 := wp_local_get cfg (fuel + 8) (8 * op + rest) (paid s op 2) limits ((stack.push (.i32 out)).push (.i32 1)) frame callers c3 1 (.i32 size) post hs
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) p8
  have p9 := normalize 8 rest r9
  have r10 := wp_local_get cfg (fuel + 9) (9 * op + rest) (paid s op 1) limits (stack.push (.i32 out)) frame callers c2 3 (.i32 1) post ha
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) p9
  have p10 := normalize 9 rest r10
  have r11 := wp_local_get cfg (fuel + 10) (10 * op + rest) s limits stack frame callers c1 0 (.i32 out) post ho
    (hc.mono (by dsimp [op]; omega)) p10
  have p11 := normalize 10 rest r11
  simpa only [roundedCode,c1,c2,c3,c4,c5,c6,c7,c8,c9,c10,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using p11

end WNear.Proofs.AllocateLayout
