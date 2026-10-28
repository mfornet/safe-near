import Proofs.StateDecodeBorshReadCopyCall
import Proofs.StateDecodeBorshReadExit

/-! Exact161 copy argument/call/drop sequences, preserving sequential aliases. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode copyDropAfter
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_added_copy(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(slotA slotB:Nat)
    (a b da db:UInt32)(count:Nat)(mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (ha:frame.locals[slotA]?=some (.i32 a))(hb:frame.locals[slotB]?=some (.i32 b))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hfi:mi.funcAddrs[951]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hw:memory.wf)(hpositive:0<count)(hcount:count<2^32)(hwidth:memory.byteSize≤2^32)
    (hr:(b+db).toNat+count≤memory.byteSize)(hbound:(a+da).toNat+count≤memory.byteSize)
    (hd:callers.length+1<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*count+25)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (copyDropAfter (paid s cfg.regularOpCost 7) cfg.regularOpCost index (a+da) (b+db) memory count)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*count+20)) (.next (atCode s limits base.toArray frame callers
      (pairArgumentsCode slotA slotB da db++[.i32_const (UInt32.ofNat count),.call 951,.drop]++code)))
      ((18*count+25)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have cr:(paid s op 7).host.gas.Credits ((18*count+18)*op+rest):=
    paid_credits s op 7 _ (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have call:=wp_copy_drop cfg fuel rest (paid s op 7) limits base frame callers code (a+da) (b+db) count mi index address memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hfi (by rw[funcs_paid];exact hf)
    hw hpositive hcount hwidth hr hbound hd cr hnext
  have arr:(base++[Value.i32 (a+da),.i32 (b+db),.i32 (UInt32.ofNat count)]).toArray=
      ((base.toArray.push (.i32 (a+da))).push (.i32 (b+db))).push (.i32 (UInt32.ofNat count)):=by
    apply Array.toList_inj.mp;simp
  have args:=wp_copy_arguments cfg (fuel+(17*count+13)) ((18*count+18)*op+rest) s limits base.toArray frame callers
    (.call 951::.drop::code) slotA slotB a b da db (UInt32.ofNat count) post ha hb
    (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega)) (by simpa only[arr,op] using call)
  simpa only[List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 13+17*count+7=17*count+20 by omega,
    show 7*cfg.regularOpCost+((18*count+18)*op+rest)=(18*count+25)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using args
theorem wp_or_copy(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (h3:frame.locals[3]?=some (.i32 r))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hfi:mi.funcAddrs[951]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature frame.inst WNear.Binary.UnwrapState.Copy.function))
    (hw:memory.wf)(hwidth:memory.byteSize≤2^32)
    (hr:(r+60).toNat+36≤memory.byteSize)(hb:((r+16)|||4).toNat+36≤memory.byteSize)
    (hd:callers.length+1<limits.maxCallDepth)(hc:s.host.gas.Credits (675*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (copyDropAfter (paid s cfg.regularOpCost 9) cfg.regularOpCost index ((r+16)|||4) (r+60) memory 36)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+634) (.next (atCode s limits base.toArray frame callers
      (orCopyArgumentsCode++[.call 951,.drop]++code))) (675*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have cr:(paid s op 9).host.gas.Credits (666*op+rest):=
    paid_credits s op 9 _ (hc.mono (by dsimp[op];omega))
  have call:=wp_copy_drop cfg fuel rest (paid s op 9) limits base frame callers code ((r+16)|||4) (r+60) 36 mi index address memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hfi (by rw[funcs_paid];exact hf)
    hw (by decide) (by decide) hwidth hr hb hd cr hnext
  have arr:(base++[Value.i32 ((r+16)|||4),.i32 (r+60),.i32 (UInt32.ofNat 36)]).toArray=
      ((base.toArray.push (.i32 ((r+16)|||4))).push (.i32 (r+60))).push (.i32 36):=by
    apply Array.toList_inj.mp;simp
  have args:=wp_or_copy_arguments cfg (fuel+625) (666*op+rest) s limits base.toArray frame callers
    (.call 951::.drop::code) r post h3 (hc.mono (by dsimp[op];omega))
    (by simpa only[arr,Nat.reduceMul,Nat.reduceAdd,op] using call)
  simpa only[List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 9*cfg.regularOpCost+(666*op+rest)=675*cfg.regularOpCost+rest by dsimp[op];omega] using args
end WNear.Proofs.StateDecodeBorshRead
