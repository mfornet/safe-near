import Binary.StateDecodePrefix
import Proofs.StateDecodePrefixLeavesRecordCall
import NearVM.MeteredScalarRules

/-! Actual316 arguments and complete764 length-record invocation. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

def lengthAfter (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (scratch count : UInt32) :=
  StateDecodePrefixLeaves.recordCallAfter cfg (paid s cfg.regularOpCost 4) i m (scratch+24) count

theorem wp_length_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (scratch count : UInt32) (mi : ModuleInst) (i address : Nat) (m : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 scratch)) (h3 : frame.locals[3]?=some (.i32 count))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some i) (he : s.mems[i]?=some m)
    (hfi : mi.funcAddrs[764]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodePrefixLeaves.recordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.recordFunction))
    (hw : m.wf) (hb : (scratch+24).toNat+8≤m.byteSize) (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits (20*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (lengthAfter cfg s i m scratch count) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+12) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.lengthArguments++code)))
      (20*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let args:=paid s op 4
  have call:=StateDecodePrefixLeaves.wp_call_record cfg fuel rest args limits base frame callers code (scratch+24) count mi i address m post
    (by rw[modules_paid];exact hm) hfi (by rw[funcs_paid];exact hf) hi (by rw[mems_paid];exact he) hw hb hd
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hnext
  have arr : (base++[Value.i32 (scratch+24),.i32 count]).toArray=(base.toArray.push (.i32 (scratch+24))).push (.i32 count):=by
    apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+8) (.next (atCode args limits ((base.toArray.push (.i32 (scratch+24))).push (.i32 count)) frame callers (.call 764::code))) (16*op+rest) post:=by
    simpa only[arr,op] using call
  have countGet:=wp_local_get cfg (fuel+8) (16*op+rest) (paid s op 3) limits (base.toArray.push (.i32 (scratch+24))) frame callers (.call 764::code) 3 (.i32 count) post h3
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) cn
  have add:=wp_i32_add cfg (fuel+9) (op+(16*op+rest)) (paid s op 2) limits base.toArray frame callers (.local_get 3::.call 764::code) scratch 24 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) countGet
  have constant:=wp_i32_const cfg (fuel+10) (op+(op+(16*op+rest))) (paid s op 1) limits (base.toArray.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 3::.call 764::code) 24 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get:=wp_local_get cfg (fuel+11) (op+(op+(op+(16*op+rest)))) s limits base.toArray frame callers
    (.i32_const 24::.i32_binop .add::.local_get 3::.call 764::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp[op];omega)) constant
  simpa only[WNear.Binary.StateDecodePrefix.lengthArguments,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(16*op+rest))))=20*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodePrefix
