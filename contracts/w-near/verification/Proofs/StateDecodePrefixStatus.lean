import Binary.StateDecodePrefix
import Proofs.StateDecodePrefixLeavesWordResult
import NearVM.MeteredWordRules
import NearVM.MeteredNumericRules
import NearVM.MeteredLoopRules

/-! Actual316 packed-word status and positive-count branch. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open StateDecodePrefixLeaves (packedWord)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def statusFrame (frame : CallFrame) (word : UInt32) := {frame with locals:=frame.locals.set! 4 (.i64 (packedWord word))}
def countFrame (frame : CallFrame) (word : UInt32) := {frame with locals:=frame.locals.set! 3 (.i32 word)}

theorem packed_status_zero (word : UInt32) : packedWord word &&& 1=0 := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and,UInt64.toNat_ofNat,Nat.reducePow,Nat.reduceMod,
    StateDecodePrefixLeaves.packedWord_nat,Nat.and_one_is_mod]
  omega

theorem packed_count (word : UInt32) : (packedWord word >>> 8).toUInt32=word := by
  apply UInt32.toNat_inj.mp
  simp only [UInt64.toNat_toUInt32,UInt64.toNat_shiftRight,UInt64.toNat_ofNat,Nat.reducePow,Nat.reduceMod,
    StateDecodePrefixLeaves.packedWord_nat,Nat.shiftRight_eq_div_pow]
  have h:=word.toNat_lt
  omega

theorem wp_word_status (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (word : UInt32) (post : Post)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack (statusFrame frame word) callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits (stack.push (.i64 (packedWord word))) frame callers
      (WNear.Binary.StateDecodePrefix.wordStatus++code))) (6*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:=statusFrame frame word
  have branch:=wp_br_if_zero cfg fuel rest (paid s op 5) limits stack f callers code 0 post
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) hnext
  have z32:=wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 4) limits stack f callers (.br_if 0::code) 1 post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only [Numeric.bool,show ((1:UInt32)==0)=false from rfl,Bool.false_eq_true,ite_false,paid,op] using branch)
  have z64:=wp_i64_eqz cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits stack f callers (.i32_eqz::.br_if 0::code) 0 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only [Numeric.bool,beq_self_eq_true,ite_true,paid,op] using z32)
  have calculation : Numeric.ibinop64 .and (packedWord word) 1=.ok 0 := by
    simp only [Numeric.ibinop64,packed_status_zero]
  have mask:=wp_i64_binop_ok cfg (fuel+3) (op+(op+(op+rest))) (paid s op 2) limits stack f callers
    (.i64_eqz::.i32_eqz::.br_if 0::code) .and (packedWord word) 1 0 post calculation
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) z64
  have constant:=wp_i64_const cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 1) limits
    (stack.push (.i64 (packedWord word))) f callers (.i64_binop .and::.i64_eqz::.i32_eqz::.br_if 0::code) 1 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) mask
  have tee:=wp_local_tee cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) s limits stack frame callers
    (.i64_const 1::.i64_binop .and::.i64_eqz::.i32_eqz::.br_if 0::code) 4 (.i64 (packedWord word)) post
    (hc.mono (by dsimp[op];omega)) constant
  simpa only [WNear.Binary.StateDecodePrefix.wordStatus,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+rest)))))=6*cfg.regularOpCost+rest by dsimp[op];omega] using tee

private def zeroTail : Expr := [.local_get 0,.i64_const 4294967296,.store .i64 none {align:=2,offset:=0},
  .local_get 0,.i32_const 8,.i32_binop .add,.i64_const 0,.store .i64 none {align:=2,offset:=0},.br 4]

theorem wp_nonzero_count (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (word : UInt32) (post : Post)
    (h4 : frame.locals[4]?=some (.i64 (packedWord word))) (hn : word≠0)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack (countFrame frame word) callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (.block .empty WNear.Binary.StateDecodePrefix.nonzero::code)))
      (6*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let bf:=emptyBlockFrame frame stack.size code
  let cf:=countFrame frame word
  have branch:=wp_br_if_block_nonzero cfg fuel rest (paid s op 5) limits stack cf callers code zeroTail word post hn
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) hnext
  have tee:=wp_local_tee cfg (fuel+1) (op+rest) (paid s op 4) limits stack bf callers (.br_if 0::zeroTail) 3 (.i32 word) post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) branch
  have wrap:=wp_i32_wrap_i64 cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits stack bf callers
    (.local_tee 3::.br_if 0::zeroTail) (packedWord word >>> 8) post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only [packed_count,paid,op,Nat.add_assoc,Nat.reduceAdd] using tee)
  have calculation : Numeric.ibinop64 .shr_u (packedWord word) 8=.ok (packedWord word >>> 8) := by simp [Numeric.ibinop64]
  have shift:=wp_i64_binop_ok cfg (fuel+3) (op+(op+(op+rest))) (paid s op 2) limits stack bf callers
    (.cvt .i32_wrap_i64::.local_tee 3::.br_if 0::zeroTail) .shr_u (packedWord word) 8 (packedWord word >>> 8) post calculation
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) wrap
  have constant:=wp_i64_const cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 1) limits
    (stack.push (.i64 (packedWord word))) bf callers (.i64_binop .shr_u::.cvt .i32_wrap_i64::.local_tee 3::.br_if 0::zeroTail) 8 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) shift
  have get:=wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) s limits stack bf callers
    (.i64_const 8::.i64_binop .shr_u::.cvt .i32_wrap_i64::.local_tee 3::.br_if 0::zeroTail) 4 (.i64 (packedWord word)) post h4
    (hc.mono (by dsimp[op];omega)) constant
  have inner : WP cfg (fuel+6) (.next (atCode s limits stack bf callers WNear.Binary.StateDecodePrefix.nonzero)) (6*cfg.regularOpCost+rest) post := by
    simpa only [WNear.Binary.StateDecodePrefix.nonzero,zeroTail,List.cons_append,List.nil_append,
      show cfg.regularOpCost+(op+(op+(op+(op+(op+rest)))))=6*cfg.regularOpCost+rest by dsimp[op];omega] using get
  exact wp_block_empty cfg (fuel+6) _ s limits stack frame callers _ code post hc inner

/-- Both loaded values remain in their actual updated local slots after the
accepted capacity comparison branches out of its block. -/
def enoughFrame (frame : CallFrame) (memory : Memory) (slice scratch : UInt32) :=
  {frame with locals:=(frame.locals.set! 5 (.i32 (readI32 memory (slice.toNat+4)))).set! 3 (.i32 (readI32 memory (scratch.toNat+28)))}
private def enoughFailure := WNear.Binary.StateDecodePrefix.enough.drop 8
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_enough (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (slice scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hb1 : slice.toNat+4+4≤memory.byteSize) (hb2 : scratch.toNat+28+4≤memory.byteSize)
    (henough : (readI32 memory (scratch.toNat+28)).toNat≤(readI32 memory (slice.toNat+4)).toNat)
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits stack
      (enoughFrame frame memory slice scratch) callers code)) rest post) :
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers
      (.block .empty WNear.Binary.StateDecodePrefix.enough::code))) (8*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let len:=readI32 memory (slice.toNat+4)
  let count:=readI32 memory (scratch.toNat+28)
  let bf:=emptyBlockFrame frame stack.size code
  let f5:={bf with locals:=bf.locals.set! 5 (.i32 len)}
  let ff:=enoughFrame frame memory slice scratch
  let inner:={f5 with locals:=f5.locals.set! 3 (.i32 count)}
  have yes : Numeric.bool (Numeric.irelop32 .ge_u len count)≠0 := by
    have cmp : Numeric.irelop32 .ge_u len count=true := by
      simp only [Numeric.irelop32,decide_eq_true_eq]
      exact henough
    simp only [cmp,Numeric.bool,ite_true]
    decide
  have branch:=wp_br_if_block_nonzero cfg fuel rest (paid s op 7) limits stack ff callers code enoughFailure
    (Numeric.bool (Numeric.irelop32 .ge_u len count)) post yes
    (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))) hnext
  have rel:=wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 6) limits stack inner callers
    (.br_if 0::enoughFailure) .ge_u len count post (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) (by simpa only [paid,op,inner,f5,bf,ff,enoughFrame,emptyBlockFrame] using branch)
  have tee3:=wp_local_tee cfg (fuel+2) (op+(op+rest)) (paid s op 5) limits (stack.push (.i32 len)) f5 callers
    (.i32_relop .ge_u::.br_if 0::enoughFailure) 3 (.i32 count) post
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) rel
  have mm4 : (paid s op 4).modules[f5.inst]?=some mi := by rw[paid_modules];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw[paid_mems];exact he
  have loadCount:=wp_i32_load cfg (fuel+3) (op+(op+(op+rest))) (paid s op 4) limits (stack.push (.i32 len)) f5 callers
    (.local_tee 3::.i32_relop .ge_u::.br_if 0::enoughFailure) {align:=2,offset:=28} scratch mi index memory post
    mm4 hi me4 hb2 (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) tee3
  have h2f : f5.locals[2]?=some (.i32 scratch) := by simp[f5,bf,emptyBlockFrame,h2]
  have getScratch:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 3) limits (stack.push (.i32 len)) f5 callers
    (.load .i32 none {align:=2,offset:=28}::.local_tee 3::.i32_relop .ge_u::.br_if 0::enoughFailure)
    2 (.i32 scratch) post h2f (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) loadCount
  have tee5:=wp_local_tee cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) (paid s op 2) limits stack bf callers
    (.local_get 2::.load .i32 none {align:=2,offset:=28}::.local_tee 3::.i32_relop .ge_u::.br_if 0::enoughFailure)
    5 (.i32 len) post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) getScratch
  have mm1 : (paid s op 1).modules[bf.inst]?=some mi := by rw[paid_modules];exact hm
  have me1 : (paid s op 1).mems[index]?=some memory := by rw[paid_mems];exact he
  have loadLen:=wp_i32_load cfg (fuel+6) (op+(op+(op+(op+(op+(op+rest)))))) (paid s op 1) limits stack bf callers
    (.local_tee 5::.local_get 2::.load .i32 none {align:=2,offset:=28}::.local_tee 3::.i32_relop .ge_u::.br_if 0::enoughFailure)
    {align:=2,offset:=4} slice mi index memory post mm1 hi me1 hb1
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) tee5
  have get:=wp_local_get cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+rest))))))) s limits stack bf callers
    (.load .i32 none {align:=2,offset:=4}::.local_tee 5::.local_get 2::.load .i32 none {align:=2,offset:=28}::
      .local_tee 3::.i32_relop .ge_u::.br_if 0::enoughFailure) 1 (.i32 slice) post h1
    (hc.mono (by dsimp[op];omega)) loadLen
  have inside : WP cfg (fuel+8) (.next (atCode s limits stack bf callers WNear.Binary.StateDecodePrefix.enough)) (8*cfg.regularOpCost+rest) post := by
    simpa only [WNear.Binary.StateDecodePrefix.enough,enoughFailure,List.drop_succ_cons,List.drop_zero,
      show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(op+rest)))))))=8*cfg.regularOpCost+rest by dsimp[op];omega] using get
  exact wp_block_empty cfg (fuel+8) _ s limits stack frame callers _ code post hc inside
end WNear.Proofs.StateDecodePrefix
