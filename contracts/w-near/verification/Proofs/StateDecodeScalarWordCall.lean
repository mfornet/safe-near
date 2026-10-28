import Proofs.StateDecodeScalarArguments
import Proofs.StateDecodeWordsFrame

/-! Actual fixed-width word decoder call after the scalar take operation. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl |succ n ih=>exact ih

def wordAfter (cfg : WasmConfig) (s : Store NearState) (wide : Bool) (index : Nat) (memory : Memory) (scratch pointer : UInt32) :=
  StateDecodeWords.callAfter wide cfg (paid s cfg.regularOpCost 7) index memory
    (scratch+WNear.Binary.StateDecodeScalar.wordOffset wide) pointer

theorem wp_word_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (wide : Bool) (scratch pointer : UInt32) (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hfi : mi.funcAddrs[if wide then 694 else 710]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeWords.signature frame.inst (WNear.Binary.StateDecodeWords.function wide)))
    (hwf : memory.wf) (hwidth : memory.byteSize≤2^32)
    (hb : scratch.toNat+(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+8≤memory.byteSize)
    (hsource : pointer.toNat+StateDecodeWords.widthNat wide≤memory.byteSize)
    (ho : (scratch+WNear.Binary.StateDecodeScalar.wordOffset wide).toNat+(StateDecodeWords.widthNat wide+1)≤memory.byteSize)
    (hp : readI32 memory (scratch.toNat+(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat)=pointer)
    (hn : readI32 memory (scratch.toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4))=StateDecodeWords.width wide)
    (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((StateDecodeWords.bodyCost wide+18)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (wordAfter cfg s wide index memory scratch pointer) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+StateDecodeWords.bodySteps wide+9) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodeScalar.wordArguments wide++code)))
      ((StateDecodeWords.bodyCost wide+18)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let args := paid s op 7
  let out := scratch+WNear.Binary.StateDecodeScalar.wordOffset wide
  have mm : args.modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me : args.mems[index]?=some memory := by rw [mems_paid];exact he
  have mf : args.funcs[address]?=some (.wasm WNear.Binary.StateDecodeWords.signature frame.inst (WNear.Binary.StateDecodeWords.function wide)) := by rw [funcs_paid];exact hf
  have ca := paid_credits s op 7 ((StateDecodeWords.bodyCost wide+11)*op+rest) (hc.mono (by simp only [Nat.add_mul,op];omega))
  have next : WP cfg fuel (.next (atCode (StateDecodeWords.callAfter wide cfg args index memory out pointer) limits base.toArray frame callers code)) rest post := hnext
  have call := StateDecodeWords.wp_call wide cfg fuel rest args limits base frame callers code out pointer mi index address memory post
    mm hfi mf hi me hwf hsource ho hwidth hd ca next
  let argv := ((base.toArray.push (.i32 out)).push
    (.i32 (readI32 memory (scratch.toNat+(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat)))).push
    (.i32 (readI32 memory (scratch.toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4))))
  have operands : (base++[Value.i32 out,.i32 pointer,.i32 (StateDecodeWords.width wide)]).toArray=argv := by
    dsimp only [argv]
    rw [hp,hn];apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+StateDecodeWords.bodySteps wide+2) (.next (atCode args limits argv frame callers
      (.call (if wide then 694 else 710)::code))) ((StateDecodeWords.bodyCost wide+11)*op+rest) post := by
    rw [operands] at call
    exact call
  have arguments := wp_word_arguments cfg (fuel+StateDecodeWords.bodySteps wide+2) ((StateDecodeWords.bodyCost wide+11)*op+rest)
    s limits base.toArray frame callers (.call (if wide then 694 else 710)::code) wide scratch 0 0 mi index memory post h2 hm hi he
    (by omega) (by omega) (hc.mono (by simp only [Nat.add_mul,op];omega)) cn
  have ce : 7*cfg.regularOpCost+((StateDecodeWords.bodyCost wide+11)*op+rest)=
      (StateDecodeWords.bodyCost wide+18)*cfg.regularOpCost+rest := by simp only [Nat.add_mul,op];omega
  rw [ce] at arguments
  simpa only [word_code_eq,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using arguments
end WNear.Proofs.StateDecodeScalar
