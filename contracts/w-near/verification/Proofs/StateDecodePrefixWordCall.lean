import Proofs.StateDecodePrefixGuard
import Proofs.StateDecodePrefixLeavesWordResult

/-! Actual f316 cached-slice arguments and complete f765 typed word read. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih

def wordAfter (cfg : WasmConfig) (s : Store NearState) := StateDecodePrefixLeaves.wordCallAfter cfg (paid s cfg.regularOpCost 4)

theorem wp_prefix_word_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (scratch pointer : UInt32) (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hfi : mi.funcAddrs[765]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodePrefixLeaves.wordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.wordFunction))
    (hb : scratch.toNat+48≤memory.byteSize) (hptr : readI32 memory (scratch.toNat+40)=pointer)
    (hlen : readI32 memory (scratch.toNat+44)=4) (hp : pointer.toNat+4≤memory.byteSize)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (30*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (wordAfter cfg s) limits
      (base++[Value.i64 (StateDecodePrefixLeaves.packedWord (readI32 memory pointer.toNat))]).toArray frame callers code)) rest post) :
    WP cfg (fuel+25) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.wordArguments++code)))
      (30*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have mm4 : (paid s op 4).modules[frame.inst]?=some mi := by rw [paid_modules];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw [paid_mems];exact he
  have mf4 : (paid s op 4).funcs[address]?=some (.wasm WNear.Binary.StateDecodePrefixLeaves.wordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.wordFunction) := by rw [paid_funcs];exact hf
  have call:=StateDecodePrefixLeaves.wp_call_word cfg fuel rest (paid s op 4) limits base frame callers code pointer mi index address memory post
    mm4 hfi mf4 hi me4 hp hd (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hnext
  have arr : (base++[Value.i32 pointer,.i32 4]).toArray=(base.toArray.push (.i32 pointer)).push (.i32 4) := by
    apply Array.toList_inj.mp;simp
  rw [arr] at call
  have mm3 : (paid s op 3).modules[frame.inst]?=some mi := by rw[paid_modules];exact hm
  have me3 : (paid s op 3).mems[index]?=some memory := by rw[paid_mems];exact he
  have load44:=wp_i32_load cfg (fuel+21) (26*op+rest) (paid s op 3) limits (base.toArray.push (.i32 pointer)) frame callers
    (.call 765::code) {align:=2,offset:=44} scratch mi index memory post mm3 hi me3 (by change scratch.toNat+44+4≤memory.byteSize;omega)
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only [hlen,paid,op] using call)
  have get44:=wp_local_get cfg (fuel+22) (op+(26*op+rest)) (paid s op 2) limits (base.toArray.push (.i32 pointer)) frame callers
    (.load .i32 none {align:=2,offset:=44}::.call 765::code) 2 (.i32 scratch) post h2
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) load44
  have mm1 : (paid s op 1).modules[frame.inst]?=some mi := by rw[paid_modules];exact hm
  have me1 : (paid s op 1).mems[index]?=some memory := by rw[paid_mems];exact he
  have load40:=wp_i32_load cfg (fuel+23) (op+(op+(26*op+rest))) (paid s op 1) limits base.toArray frame callers
    (.local_get 2::.load .i32 none {align:=2,offset:=44}::.call 765::code) {align:=2,offset:=40} scratch mi index memory post mm1 hi me1 (by change scratch.toNat+40+4≤memory.byteSize;omega)
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) (by simpa only [hptr,paid,op] using get44)
  have get40:=wp_local_get cfg (fuel+24) (op+(op+(op+(26*op+rest)))) s limits base.toArray frame callers
    (.load .i32 none {align:=2,offset:=40}::.local_get 2::.load .i32 none {align:=2,offset:=44}::.call 765::code) 2 (.i32 scratch) post h2
    (hc.mono (by dsimp[op];omega)) load40
  simpa only [WNear.Binary.StateDecodePrefix.wordArguments,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(26*op+rest))))=30*cfg.regularOpCost+rest by dsimp[op];omega] using get40
end WNear.Proofs.StateDecodePrefix
