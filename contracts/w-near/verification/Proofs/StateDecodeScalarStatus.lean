import Binary.StateDecodeScalar
import Proofs.StorePairCallerState
import NearVM.MeteredByteMemoryRules
import NearVM.MeteredNumericRules
import NearVM.MeteredLoopRules

/-! The real scalar decoder status-byte load skips its invalid-value branch. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_status_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hb : scratch.toNat+(WNear.Binary.StateDecodeScalar.wordOffset wide).toNat+1≤memory.byteSize)
    (hz : memory.read8 (scratch.toNat+(WNear.Binary.StateDecodeScalar.wordOffset wide).toNat)=0)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeScalar.statusGuard wide++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let byte := readByteWord memory (scratch.toNat+(WNear.Binary.StateDecodeScalar.wordOffset wide).toNat)
  have zero : byte=0 := by simp [byte,hz]
  have br := wp_br_if_zero cfg fuel rest (paid s op 4) limits stack frame callers code 1 post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) hnext
  have rel := wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 3) limits stack frame callers (.br_if 1::code) .eq byte 1 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [zero,show Numeric.bool (Numeric.irelop32 .eq 0 1)=0 by decide,paid,op] using br)
  have con := wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits (stack.push (.i32 byte)) frame callers
    (.i32_relop .eq::.br_if 1::code) 1 post (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) rel
  have mm : (paid s op 1).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me : (paid s op 1).mems[index]?=some memory := by rw [mems_paid];exact he
  have load := wp_i32_load8_unsigned cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers
    (.i32_const 1::.i32_relop .eq::.br_if 1::code) {align:=0,offset:=(WNear.Binary.StateDecodeScalar.wordOffset wide).toNat}
    scratch mi index memory post mm hi me hb (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) con
  have get := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.load .i32 (some ⟨8,false⟩) {align:=0,offset:=(WNear.Binary.StateDecodeScalar.wordOffset wide).toNat}::.i32_const 1::.i32_relop .eq::.br_if 1::code)
    2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) load
  simpa only [WNear.Binary.StateDecodeScalar.statusGuard,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp [op];omega] using get
end WNear.Proofs.StateDecodeScalar
