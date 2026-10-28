import Proofs.StateReadStorageOuterArguments
import Proofs.StateReadStorageOuterExit
import Proofs.StateReadResultFrame

/-! Actual548 argument setup, accepted f498 call, remaining block exit and restore. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode StateReadResult.callAfter readI32

def tailAfter (s : Store NearState) (op index globalIndex : Nat) (memory : Memory) (out scratch : UInt32) :=
  setGlobal (paid (StateReadResult.callAfter (paid s op 7) op index memory out (scratch+16)) op 4)
    globalIndex (.i32 (scratch+32))
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (out scratch : UInt32) (mi : ModuleInst) (index globalIndex address : Nat)
    (memory : Memory) (global : GlobalInst) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h3 : frame.locals[3]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hgi : mi.globalAddrs[0]?=some globalIndex)
    (hg : s.globals[globalIndex]?=some global)
    (hfi : mi.funcAddrs[498]?=some address)
    (hfn : s.funcs[address]?=some (.wasm WNear.Binary.StateRead.resultSignature frame.inst WNear.Binary.StateRead.resultFunction))
    (hwf : memory.wf) (hob : out.toNat+8≤memory.byteSize) (hsb : (scratch+16).toNat+8≤memory.byteSize)
    (hoh : (out+8).toNat+4≤memory.byteSize) (hsh : (scratch+16+8).toNat+4≤memory.byteSize)
    (htag : readI32 memory (scratch+16).toNat≠0) (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits (38*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (tailAfter s cfg.regularOpCost index globalIndex memory out scratch)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+30) (.next (atCode s limits base.toArray
      (emptyBlockFrame frame base.toArray.size (WNear.Binary.StateReadStorageOuter.restore++code)) callers
      (WNear.Binary.StateReadStorageOuter.optionArguments++[.call 498])))
      (38*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let outer := emptyBlockFrame frame base.toArray.size (WNear.Binary.StateReadStorageOuter.restore++code)
  let args := paid s op 7
  let done := StateReadResult.callAfter args op index memory out (scratch+16)
  have fields : done.modules=args.modules ∧ done.globals=args.globals := by
    have f := StateReadResult.after_fields (StateReadResult.entered args op) op index memory out (scratch+16)
    simpa only [done,StateReadResult.callAfter,StateReadResult.entered,chargedStore] using And.intro f.2.1 f.2.2.2
  have dm : done.modules[frame.inst]?=some mi := by rw [fields.1,paid_modules];exact hm
  have dg : done.globals[globalIndex]?=some global := by rw [fields.2,paid_globals];exact hg
  have ca : args.host.gas.Credits (27*op+(4*op+rest)) := paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))
  have cd := StateReadResult.callAfter_credits args op index (4*op+rest) memory out (scratch+16) ca
  have exn : WP cfg fuel (.next (atCode (setGlobal (paid done op 4) globalIndex (.i32 (scratch+32))) limits base.toArray frame callers code)) rest post := by
    simpa only [tailAfter,done,args,op] using hnext
  have exit := wp_exit cfg fuel rest done limits base.toArray frame callers code scratch mi globalIndex global post h3 dm hgi dg cd exn
  have am : args.modules[outer.inst]?=some mi := by rw [paid_modules];exact hm
  have ae : args.mems[index]?=some memory := by rw [paid_mems];exact hmem
  have af : args.funcs[address]?=some (.wasm WNear.Binary.StateRead.resultSignature outer.inst WNear.Binary.StateRead.resultFunction) := by rw [paid_funcs];exact hfn
  have callee := StateReadResult.wp_call cfg (fuel+5) (4*op+rest) args limits base outer callers [] out (scratch+16) 1055256 68 1056324 mi index address memory post
    am hi ae hfi af hwf hob hsb hoh hsh htag hd ca exit
  have arr : (base++[Value.i32 out,.i32 (scratch+16),.i32 1055256,.i32 68,.i32 1056324]).toArray=
      (((((base.toArray.push (.i32 out)).push (.i32 (scratch+16))).push (.i32 1055256)).push (.i32 68)).push (.i32 1056324)) := by apply Array.toList_inj.mp;simp
  have next : WP cfg ((fuel+5)+18) (.next (atCode args limits
      (((((base.toArray.push (.i32 out)).push (.i32 (scratch+16))).push (.i32 1055256)).push (.i32 68)).push (.i32 1056324))
      outer callers [.call 498])) (27*op+(4*op+rest)) post := by
    simpa only [arr,op] using callee
  have arguments := wp_option_arguments cfg ((fuel+5)+18) (27*op+(4*op+rest)) s limits base.toArray outer callers [.call 498] scratch out post h3 h0
    (hc.mono (by dsimp [op];omega)) next
  have ce : 7*cfg.regularOpCost+(27*op+(4*op+rest))=38*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [ce,Nat.add_assoc,Nat.reduceAdd] using arguments
end WNear.Proofs.StateReadStorageOuter
