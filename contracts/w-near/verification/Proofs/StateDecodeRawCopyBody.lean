import Proofs.StateDecodeRawCopyTail
import Proofs.StateDecodeRawCopyFrame
import Proofs.StateDecodeRawCopyGlobals
import Proofs.StateDecodeRawRecordTransport
import Proofs.StateDecodeRawCopyGas

/-! Complete deployed769 positive alignment-one body. Original raw-wrapper
heap data supplies the actual post752 allocator domain through its proved bridge. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode allocated769 after769 laidOutMemory memory770 lowMemory769 reserved769
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih

private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem tables_paid (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_copy_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (a581 a236 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p a581 a236) (ha : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 (scratch p+16))) (h1 : frame.locals[1]?=some (.i32 p.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (hs : 4≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some (laidOutMemory p))
    (hg : s.globals[p.globalIndex]?=some {p.globalRaw with value:=.i32 (scratch p)})
    (hd : callers.length+6<limits.maxCallDepth) (hc : s.host.gas.Credits (436*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (after769 cfg s p) limits base.toArray (reserved769Frame frame p) callers code)) rest post) :
    WP cfg (fuel+353) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeRaw.body769++code)))
      (436*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:=reserved769Frame frame p
  let q:=actualPositive p
  have h3 : f.locals[3]?=some (.i32 (scratch769 p)):=by simp[f,reserved769Frame,show 3<frame.locals.size by omega]
  have h0f : f.locals[0]?=some (.i32 (scratch p+16)):=by simp[f,reserved769Frame,h0]
  have h1f : f.locals[1]?=some (.i32 p.size):=by simp[f,reserved769Frame,h1]
  have h2f : f.locals[2]?=some (.i32 1):=by simp[f,reserved769Frame,h2]
  have n:=stack_numbers p hn
  have r:=record_numbers p hn
  have lo:=hn.spLower
  have sb:=hn.spBound
  have ca : (arguments769 s op p).host.gas.Credits (413*op+(12*op+rest)) :=
    (arguments769_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2
  have cc : (allocated769 cfg s p).host.gas.Credits (12*op+rest):=by
    unfold allocated769
    exact recordCallAfter_credits cfg (arguments769 s op p) q (out770 p) _ ca
  have af:=allocated769_fields cfg s p
  have cm : (allocated769 cfg s p).modules[f.inst]?=some p.mi := by
    rw[af.2.1];exact hcode.record.allocation.search.module
  have ag : (allocated769 cfg s p).globals[p.globalIndex]?=some p.global := by
    rw[allocated769_globals cfg s p hn hg]
    exact arguments769_global s op p hn hg
  have shape:=memory770_spec p hn
  have source : (scratch769 p).toNat+16≤(memory770 p).byteSize := by rw[shape.2.1,n.2.1];omega
  have target : (scratch p+16).toNat+8≤(memory770 p).byteSize := by rw[shape.2.1,r.2.1];omega
  have addr : (scratch769 p).toNat+8=(out770 p).toNat := by rw[n.2.1,r.1];omega
  have eqLow : copyLowMemory (memory770 p) (scratch769 p) (scratch p+16)=lowMemory769 p := by
    simp only[copyLowMemory,lowMemory769,addr]
  have spRestore : scratch769 p+16=scratch p := UInt32.sub_add_cancel _ _
  have tail:=wp_copy_tail cfg fuel rest (allocated769 cfg s p) limits base.toArray f callers code
    (scratch769 p) (scratch p+16) p.mi p.memoryIndex p.globalIndex (memory770 p) p.global post h0f h3 cm
    hcode.record.allocation.search.memoryIndex hcode.record.allocation.globalIndex (allocated769_memory cfg s p hm) ag shape.1 source target cc
    (by simpa only[copyTailAfter,highCopyStore,lowCopyStore,eqLow,after769,highCopied769,lowCopied769,spRestore,op] using hnext)
  have rc : RecordCode (reserved769 s op p) f.inst q a581 a236 p.address310 := by
    have old:=hcode.recordActual s frame.inst p a581 a236 hn
    apply RecordCode.transport s (reserved769 s op p) frame.inst q a581 a236 p.address310 old
    · simp only[reserved769,setGlobal,funcs_paid]
    · simp only[reserved769,setGlobal,modules_paid]
    · simp only[reserved769,setGlobal,tables_paid]
  have rm : (reserved769 s op p).mems[p.memoryIndex]?=some (laidOutMemory p) := by
    simp only[reserved769,setGlobal,mems_paid];exact hm
  have rg : (reserved769 s op p).globals[p.globalIndex]?=some p.global := by
    have g:=arguments769_global s op p hn hg
    simpa only[arguments769,globals_paid] using g
  have call:=wp_invoke_record cfg (fuel+12) (12*op+rest) (reserved769 s op p) limits base f callers
    (WNear.Binary.StateDecodeRaw.lowCopy++WNear.Binary.StateDecodeRaw.highCopy++WNear.Binary.StateDecodeRaw.restore 3 16++code)
    q (scratch769 p) a581 a236 p.address310 p.address770 post (allocation_native p hn) rc ha h1f h2f h3 rm rg
    (by change p.global.value=.i32 p.sp;rw[hn.childGlobal])
    (by change (out770 p).toNat+8≤(laidOutMemory p).byteSize;rw[(layout_spec p hn).2.1,r.1];omega)
    hcode.index770 (by simp only[reserved769,setGlobal,funcs_paid];exact hcode.function770) hd
    ((reserved769_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[invokedRecord,allocated769,arguments769,out770,op] using tail)
  have reserve:=InterfaceStack.wp_reserve cfg (fuel+348) (419*op+(12*op+rest)) s limits base.toArray frame callers
    (WNear.Binary.StateDecodeRaw.arguments770++WNear.Binary.StateDecodeRaw.lowCopy++WNear.Binary.StateDecodeRaw.highCopy++WNear.Binary.StateDecodeRaw.restore 3 16++code)
    p.mi p.globalIndex {p.globalRaw with value:=.i32 (scratch p)} (scratch p) 3 16 post
    hcode.record.allocation.search.module hcode.record.allocation.globalIndex hg rfl (hc.mono (by dsimp[op];omega))
    (by simpa only[reserved769,f,reserved769Frame,scratch769,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using call)
  simpa only[WNear.Binary.StateDecodeRaw.body769,WNear.Binary.StateDecodeRaw.setup,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 5*cfg.regularOpCost+(419*op+(12*op+rest))=436*cfg.regularOpCost+rest by dsimp[op];omega] using reserve
end WNear.Proofs.StateDecodeRaw
