import Binary.StateDecodePrefix
import Proofs.AllocateVectorSteps
import NearVM.MeteredNumericRules
import NearVM.MeteredLoopRules

/-! Actual f316 accepted initial length check, before any payload access. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open AllocateVector (loadedFrame)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_length_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (slice : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hb : slice.toNat+4+4≤memory.byteSize) (hn : 4≤(readI32 memory (slice.toNat+4)).toNat)
    (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack
      (loadedFrame frame 3 (readI32 memory (slice.toNat+4))) callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefix.lengthGuard++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let len:=readI32 memory (slice.toNat+4)
  let ff:=loadedFrame frame 3 len
  have cmp : Numeric.irelop32 .lt_u len 4=false := by
    simp only [Numeric.irelop32,decide_eq_false_iff_not]
    change ¬len.toNat<4
    dsimp [len]
    omega
  have branch:=wp_br_if_zero cfg fuel rest (paid s op 5) limits stack ff callers code 0 post
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) hnext
  have rel:=wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 4) limits stack ff callers (.br_if 0::code) .lt_u len 4 post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only [cmp,Numeric.bool,Bool.false_eq_true,ite_false,paid,op] using branch)
  have constant:=wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 3) limits (stack.push (.i32 len)) ff callers
    (.i32_relop .lt_u::.br_if 0::code) 4 post (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) rel
  have tee:=wp_local_tee cfg (fuel+3) (op+(op+(op+rest))) (paid s op 2) limits stack frame callers
    (.i32_const 4::.i32_relop .lt_u::.br_if 0::code) 3 (.i32 len) post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) constant
  have mm : (paid s op 1).modules[frame.inst]?=some mi := by rw[paid_modules];exact hm
  have me : (paid s op 1).mems[index]?=some memory := by rw[paid_mems];exact he
  have load:=wp_i32_load cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 1) limits stack frame callers
    (.local_tee 3::.i32_const 4::.i32_relop .lt_u::.br_if 0::code) {align:=2,offset:=4} slice mi index memory post mm hi me hb
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) tee
  have get:=wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) s limits stack frame callers
    (.load .i32 none {align:=2,offset:=4}::.local_tee 3::.i32_const 4::.i32_relop .lt_u::.br_if 0::code) 1 (.i32 slice) post h1
    (hc.mono (by dsimp[op];omega)) load
  simpa only [WNear.Binary.StateDecodePrefix.lengthGuard,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+rest)))))=6*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodePrefix
