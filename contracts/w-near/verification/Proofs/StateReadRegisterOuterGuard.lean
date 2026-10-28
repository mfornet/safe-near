import Proofs.StateReadRegisterOuterSteps
import NearVM.MeteredLoopRules

/-! The actual523 Option tag test is read, wrapped and checked by guest instructions. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI64

theorem wp_present_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : scratch.toNat+8+8≤memory.byteSize)
    (hn : (readI64 memory (scratch.toNat+8)).toUInt32≠0)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateReadRegisterOuter.presentGuard++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let value := readI64 memory (scratch.toNat+8)
  have br := wp_br_if_zero cfg fuel rest (paid s op 4) limits stack frame callers code 0 post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) hnext
  have eq := wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 3) limits stack frame callers (.br_if 0::code) value.toUInt32 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega)))
    (by simpa only [Numeric.bool,show (value.toUInt32==0)=false from beq_eq_false_iff_ne.mpr hn,Bool.false_eq_true,ite_false,paid,op] using br)
  have cv := wp_i32_wrap_i64 cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers (.i32_eqz::.br_if 0::code) value post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) eq
  have mm : (paid s op 1).modules[frame.inst]?=some mi := by simpa only [paid,chargedStore] using hm
  have me : (paid s op 1).mems[index]?=some memory := by simpa only [paid,chargedStore] using hmem
  have cn : WP cfg (fuel+3) (.next (atCode (chargedStore (paid s op 1) op) limits
      (stack.push (.i64 (readI64 memory (scratch.toNat+8)))) frame callers (.cvt .i32_wrap_i64::.i32_eqz::.br_if 0::code))) (op+(op+(op+rest))) post := by
    simpa only [value,paid,op] using cv
  have ld := wp_i64_load cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers
    (.cvt .i32_wrap_i64::.i32_eqz::.br_if 0::code) {align:=3,offset:=8} scratch mi index memory post mm hi me hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) cn
  have g := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.load .i64 none {align:=3,offset:=8}::.cvt .i32_wrap_i64::.i32_eqz::.br_if 0::code) 2 (.i32 scratch) post h2
    (hc.mono (by dsimp [op];omega)) ld
  simpa only [WNear.Binary.StateReadRegisterOuter.presentGuard,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp [op];omega] using g
end WNear.Proofs.StateReadRegisterOuter
