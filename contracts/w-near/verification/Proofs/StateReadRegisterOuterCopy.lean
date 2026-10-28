import Proofs.StateReadRegisterOuterSteps
import NearVM.MeteredI32MemoryRules

/-! Actual523 finalcopy retains the read-after-high-write snapshot for arbitrary aliases. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64

def firstMemory (memory : Memory) (out scratch : UInt32) :=
  writeI32 memory (out+8).toNat (readI32 memory (scratch+32+8).toNat)
def finalMemory (memory : Memory) (out scratch : UInt32) :=
  writeI64 (firstMemory memory out scratch) out.toNat (readI64 (firstMemory memory out scratch) (scratch.toNat+32))
def copyHigh (s : Store NearState) (op index : Nat) (memory : Memory) (out scratch : UInt32) :=
  storeI32 (paid s op 10) index (out+8).toNat memory (readI32 memory (scratch+32+8).toNat)
def copyLow (s : Store NearState) (op index : Nat) (memory : Memory) (out scratch : UInt32) :=
  storeI64 (paid s op 4) index out.toNat memory (readI64 memory (scratch.toNat+32))

theorem wp_copy_high (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hs : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hr : (scratch+32+8).toNat+4≤memory.byteSize) (hw : (out+8).toNat+4≤memory.byteSize)
    (hc : s.host.gas.Credits (10*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copyHigh s cfg.regularOpCost index memory out scratch) limits stack frame callers code)) rest post) :
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadRegisterOuter.copyHigh++code)))
      (10*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let dst := out+8
  let src := scratch+32+8
  have m9 : (paid s op 9).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have e9 : (paid s op 9).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have sn : WP cfg fuel (.next (atCode (storeI32 (chargedStore (paid s op 9) op) index (dst.toNat+0) memory (readI32 memory (src.toNat+0))) limits stack frame callers code)) rest post := by
    simpa only [copyHigh,dst,src,Nat.add_zero,paid,op] using hnext
  have st := wp_i32_store cfg fuel rest (paid s op 9) limits stack frame callers code {align:=2,offset:=0} dst (readI32 memory src.toNat) mi index memory post m9 hi e9
    (by simpa only [dst,Nat.add_zero] using hw) (paid_credits s op 9 _ (hc.mono (by dsimp [op];omega))) sn
  have m8 : (paid s op 8).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have e8 : (paid s op 8).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have ld := wp_i32_load cfg (fuel+1) (op+rest) (paid s op 8) limits (stack.push (.i32 dst)) frame callers
    (.store .i32 none {align:=2,offset:=0}::code) {align:=2,offset:=0} src mi index memory post m8 hi e8
    (by simpa only [src,Nat.add_zero] using hr) (paid_credits s op 8 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [Nat.add_zero,paid,op] using st)
  have add8 := wp_i32_add cfg (fuel+2) (op+(op+rest)) (paid s op 7) limits (stack.push (.i32 dst)) frame callers
    (.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) (scratch+32) 8 post
    (paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))) ld
  have k8 := wp_i32_const cfg (fuel+3) (op+(op+(op+rest))) (paid s op 6) limits ((stack.push (.i32 dst)).push (.i32 (scratch+32))) frame callers
    (.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 8 post
    (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) add8
  have add32 := wp_i32_add cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 5) limits (stack.push (.i32 dst)) frame callers
    (.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) scratch 32 post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) k8
  have k32 := wp_i32_const cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) (paid s op 4) limits ((stack.push (.i32 dst)).push (.i32 scratch)) frame callers
    (.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 32 post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) add32
  have gs := wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+rest)))))) (paid s op 3) limits (stack.push (.i32 dst)) frame callers
    (.i32_const 32::.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 2 (.i32 scratch) post hs
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) k32
  have addOut := wp_i32_add cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+rest))))))) (paid s op 2) limits stack frame callers
    (.local_get 2::.i32_const 32::.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) out 8 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) gs
  have kOut := wp_i32_const cfg (fuel+8) (op+(op+(op+(op+(op+(op+(op+(op+rest)))))))) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.i32_binop .add::.local_get 2::.i32_const 32::.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 8 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) addOut
  have go := wp_local_get cfg (fuel+9) (op+(op+(op+(op+(op+(op+(op+(op+(op+rest))))))))) s limits stack frame callers
    (.i32_const 8::.i32_binop .add::.local_get 2::.i32_const 32::.i32_binop .add::.i32_const 8::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=0}::code) 0 (.i32 out) post ho
    (hc.mono (by dsimp [op];omega)) kOut
  simpa only [WNear.Binary.StateReadRegisterOuter.copyHigh,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(op+(op+(op+rest)))))))))=10*cfg.regularOpCost+rest by dsimp [op];omega] using go

theorem wp_copy_low (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (ho : frame.locals[0]?=some (.i32 out)) (hs : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hr : scratch.toNat+32+8≤memory.byteSize) (hw : out.toNat+8≤memory.byteSize)
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (copyLow s cfg.regularOpCost index memory out scratch) limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadRegisterOuter.copyLow++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have m3 : (paid s op 3).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have e3 : (paid s op 3).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have sn : WP cfg fuel (.next (atCode (storeI64 (chargedStore (paid s op 3) op) index (out.toNat+0) memory
      (readI64 memory (scratch.toNat+32))) limits stack frame callers code)) rest post := by
    simpa only [copyLow,Nat.add_zero,paid,op] using hnext
  have st := wp_i64_store cfg fuel rest (paid s op 3) limits stack frame callers code {align:=2,offset:=0}
    out (readI64 memory (scratch.toNat+32)) mi index memory post m3 hi e3
    (by simpa only [Nat.add_zero] using hw) (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) sn
  have m2 : (paid s op 2).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have e2 : (paid s op 2).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have ld := wp_i64_load cfg (fuel+1) (op+rest) (paid s op 2) limits (stack.push (.i32 out)) frame callers
    (.store .i64 none {align:=2,offset:=0}::code) {align:=3,offset:=32} scratch mi index memory post m2 hi e2 hr
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) st
  have gs := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.load .i64 none {align:=3,offset:=32}::.store .i64 none {align:=2,offset:=0}::code) 2 (.i32 scratch) post hs
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) ld
  have go := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.local_get 2::.load .i64 none {align:=3,offset:=32}::.store .i64 none {align:=2,offset:=0}::code) 0 (.i32 out) post ho
    (hc.mono (by dsimp [op];omega)) gs
  simpa only [WNear.Binary.StateReadRegisterOuter.copyLow,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp [op];omega] using go
end WNear.Proofs.StateReadRegisterOuter
