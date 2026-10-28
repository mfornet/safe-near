import Proofs.StateDecodeSlicesGuard
import NearVM.MeteredI32MemoryRules

/-! Generic local-word stores used by both actual slice helpers. -/
namespace WNear.Proofs.StateDecodeSlices
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def wordStore (s : Store NearState) (op index : Nat) (memory : Memory) (out word : UInt32) (offset : Nat) :=
  storeI32 (paid s op 3) index (out.toNat+offset) memory word

def binaryWord (sub : Bool) (a b : UInt32) := if sub then a-b else a+b
def binaryStore (s : Store NearState) (op index : Nat) (memory : Memory) (out a b : UInt32) (offset : Nat) (sub : Bool) :=
  storeI32 (paid s op 5) index (out.toNat+offset) memory (binaryWord sub a b)
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_word_store (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out word : UInt32) (slot offset : Nat) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (hv : frame.locals[slot]?=some (.i32 word))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hb : out.toNat+offset+4≤memory.byteSize) (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (wordStore s cfg.regularOpCost index memory out word offset) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get 0::.local_get slot::.store .i32 none {align:=2,offset}::code))) (3*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm : (paid s op 2).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me : (paid s op 2).mems[index]?=some memory := by rw [mems_paid];exact he
  have st := wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align:=2,offset} out word mi index memory post mm hi me hb
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) hnext
  have get := wp_local_get cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset}::code) slot (.i32 word) post hv (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) st
  have first := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.local_get slot::.store .i32 none {align:=2,offset}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp [op];omega)) get
  simpa only [show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp [op];omega] using first

theorem wp_binary_store (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out a b : UInt32) (left right offset : Nat) (sub : Bool)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (ha : frame.locals[left]?=some (.i32 a)) (hb : frame.locals[right]?=some (.i32 b))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hbound : out.toNat+offset+4≤memory.byteSize) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (binaryStore s cfg.regularOpCost index memory out a b offset sub) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (.local_get 0::.local_get left::.local_get right::.i32_binop (if sub then .sub else .add)::.store .i32 none {align:=2,offset}::code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm : (paid s op 4).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact he
  have st := wp_i32_store cfg fuel rest (paid s op 4) limits stack frame callers code {align:=2,offset} out (binaryWord sub a b) mi index memory post mm hi me hbound
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) hnext
  have cc := paid_credits s op 3 (op+(op+rest)) (hc.mono (by dsimp [op];omega))
  have ar : WP cfg (fuel+2) (.next (atCode (paid s op 3) limits
      (((stack.push (.i32 out)).push (.i32 a)).push (.i32 b)) frame callers
      (.i32_binop (if sub then .sub else .add)::.store .i32 none {align:=2,offset}::code))) (op+(op+rest)) post := by
    cases sub with
    | false =>
      exact wp_i32_add cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 out)) frame callers
        (.store .i32 none {align:=2,offset}::code) a b post cc st
    | true =>
      exact wp_i32_sub cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 out)) frame callers
        (.store .i32 none {align:=2,offset}::code) a b post cc st
  have gr := wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits ((stack.push (.i32 out)).push (.i32 a)) frame callers
    (.i32_binop (if sub then .sub else .add)::.store .i32 none {align:=2,offset}::code) right (.i32 b) post hb
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) ar
  have gl := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.local_get right::.i32_binop (if sub then .sub else .add)::.store .i32 none {align:=2,offset}::code) left (.i32 a) post ha
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) gr
  have go := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.local_get left::.local_get right::.i32_binop (if sub then .sub else .add)::.store .i32 none {align:=2,offset}::code) 0 (.i32 out) post h0
    (hc.mono (by dsimp [op];omega)) gl
  simpa only [show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp [op];omega] using go
end WNear.Proofs.StateDecodeSlices
