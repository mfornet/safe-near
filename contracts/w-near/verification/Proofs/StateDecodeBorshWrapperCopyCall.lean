import Proofs.StateDecodeBorshWrapperArguments
import Proofs.UnwrapStateCopyEffects
import NearVM.MeteredNumericRules

/-! Both real36-byte f951 copies made by162, with actual preparation and
returned-pointer drop. The forward copy retains arbitrary source/output aliases. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode UnwrapStateCopyEntry.callAfter
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def copyDestination(first:Bool)(out r:UInt32):=if first then r+12 else out+12
def copySource(first:Bool)(r:UInt32):=if first then (r+48)+12 else r+12
def copyArgumentCost(first:Bool):Nat:=if first then 9 else 7
def copyDropStore(first:Bool)(s:Store NearState)(op index:Nat)(memory:Memory)(out r:UInt32):=
  paid (UnwrapStateCopyEntry.callAfter (paid s op (copyArgumentCost first)) op index
    (copyDestination first out r) (copySource first r) memory 36) op 1

theorem wp_copy_call(first:Bool)(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out r:UInt32)
    (mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h2:frame.locals[2]?=some (.i32 r))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hfi:mi.funcAddrs[951]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hw:memory.wf)(hwidth:memory.byteSize≤2^32)
    (hr:(copySource first r).toNat+36≤memory.byteSize)(hb:(copyDestination first out r).toNat+36≤memory.byteSize)
    (hd:callers.length+1<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((if first then 675 else 673)*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (copyDropStore first s cfg.regularOpCost index memory out r)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(if first then 634 else 632)) (.next (atCode s limits base.toArray frame callers
      ((if first then firstCopyCode else secondCopyCode)++[.call 951,.drop]++code)))
      ((if first then 675 else 673)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let n:=copyArgumentCost first
  let t:=paid s op n
  let dest:=copyDestination first out r
  let source:=copySource first r
  let copied:=UnwrapStateCopyEntry.callAfter t op index dest source memory 36
  have ca:t.host.gas.Credits (665*op+(op+rest)):=paid_credits s op n _ (hc.mono (by cases first <;> simp only[n,copyArgumentCost,Bool.false_eq_true,ite_false,ite_true] <;> dsimp[op] <;> omega))
  have cc:copied.host.gas.Credits (op+rest):=UnwrapStateCopyEntry.callAfter_credits t op index dest source memory 36 _ (by omega) ca
  have drop:=wp_drop cfg fuel rest copied limits base.toArray frame callers code (.i32 dest) post cc hn
  have arr:(base++[Value.i32 dest]).toArray=base.toArray.push (.i32 dest):=by apply Array.toList_inj.mp;simp
  have call:=UnwrapStateCopyEntry.wp_call cfg (fuel+1) (op+rest) t limits base frame callers (.drop::code) dest source 36 address mi index memory post
    (by rw[modules_paid];exact hm) hfi (by rw[funcs_paid];exact hf) hi (by rw[mems_paid];exact he) hw
    (by omega) (by decide) hwidth hr hb hd ca (by simpa only[arr] using drop)
  have args:(base++[Value.i32 dest,.i32 source,.i32 (UInt32.ofNat 36)]).toArray=
      ((base.toArray.push (.i32 dest)).push (.i32 source)).push (.i32 36):=by apply Array.toList_inj.mp;simp
  have ready:WP cfg (fuel+625) (.next (atCode t limits
      (((base.toArray.push (.i32 dest)).push (.i32 source)).push (.i32 36)) frame callers (.call 951::.drop::code)))
      (666*op+rest) post:=by
    simpa only[args,Nat.reduceMul,Nat.reduceAdd,Nat.add_assoc,show 665*cfg.regularOpCost+(op+rest)=666*op+rest by dsimp[op];omega] using call
  cases first
  · have rule:=wp_second_copy_arguments cfg (fuel+625) (666*op+rest) s limits base.toArray frame callers (.call 951::.drop::code) out r post h0 h2
      (hc.mono (by dsimp[op];omega)) (by simpa only[t,n,copyArgumentCost,dest,source,copyDestination,copySource,Bool.false_eq_true,ite_false,op] using ready)
    simpa only[Bool.false_eq_true,ite_false,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 7*cfg.regularOpCost+(666*op+rest)=673*cfg.regularOpCost+rest by dsimp[op];omega] using rule
  · have rule:=wp_first_copy_arguments cfg (fuel+625) (666*op+rest) s limits base.toArray frame callers (.call 951::.drop::code) r post h2
      (hc.mono (by dsimp[op];omega)) (by simpa only[t,n,copyArgumentCost,dest,source,copyDestination,copySource,ite_true,op] using ready)
    simpa only[ite_true,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 9*cfg.regularOpCost+(666*op+rest)=675*cfg.regularOpCost+rest by dsimp[op];omega] using rule
end WNear.Proofs.StateDecodeBorshWrapper
