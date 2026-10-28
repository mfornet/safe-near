import Proofs.StateDecodeRawChoice
import Proofs.StateDecodeRaw767Guard
import Proofs.StateDecodeRawLayoutReadback

/-! Complete accepted deployed767 body: actual752 layout, both guards, the
selected nonzeroing769/770/310 chain, output stores and explicit caller return. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open AllocateVector (loadedFrame)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode laidOutRaw alignedRaw checkedRaw afterRaw laidOutMemory
private theorem mems_paid (s : Store NearState) (op n : Nat) : (StorePairCaller.paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_raw_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (a581 a236 : Nat) (post : Post) (hn : Native p) (hcode : Code s frame.inst p a581 a236)
    (haRoot : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.globalRaw) (hv : p.globalRaw.value=.i32 p.spRaw)
    (h0 : frame.locals[0]?=some (.i32 p.outRaw)) (h1 : frame.locals[1]?=some (.i32 p.size))
    (h2 : frame.locals[2]?=some (.i32 p.flag)) (hs : 6≤frame.locals.size)
    (ha : frame.arity=0) (hh : frame.height=base.length) (hd : callers.length+8<limits.maxCallDepth)
    (hc : s.host.gas.Credits (573*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (afterRaw cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+469) (.next (atCode s limits base.toArray frame (caller::callers) (WNear.Binary.StateDecodeRaw.body767++code)))
      (573*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let panic842:Expr:=[.local_get 4,.local_get 1,.call 842,.unreachable]
  let panic844:Expr:=[.call 844,.unreachable]
  let enclosing:=emptyBlockFrame (emptyBlockFrame frame base.toArray.size (panic842++code)) base.toArray.size panic844
  let outer:=emptyBlockFrame (reservedRawFrame frame p) base.toArray.size (panic842++code)
  let inner:=emptyBlockFrame outer base.toArray.size panic844
  let aligned:=loadedFrame inner 1 1
  let checked:=checkedRawFrame enclosing p
  let tailCode:=WNear.Binary.StateDecodeRaw.choice++rawFinish
  have ls:=checkedRaw_locals enclosing p hs h0 h2
  have cc : Code s checked.inst p a581 a236:=by simpa only[checked,checkedRawFrame_inst,enclosing,emptyBlockFrame] using hcode
  have choice:=wp_raw_choice cfg fuel rest s limits base checked caller callers p a581 a236 post hn cc haRoot hm hg
    ls.1 ls.2.1 ls.2.2.1 ls.2.2.2.1 ls.2.2.2.2.1
    (by simpa only[checked,checkedRawFrame,alignedRawFrame,reservedRawFrame,loadedFrame,Array.size_set!,enclosing,emptyBlockFrame] using hs)
    (by simpa only[checked,checkedRawFrame_arity,enclosing,emptyBlockFrame] using ha)
    (by simpa only[checked,checkedRawFrame_height,enclosing,emptyBlockFrame] using hh) hd hc hnext
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have sb:=hn.spBound
  have shape:=layout_spec p hn
  have words:=layout_words p hn
  have ac:=hcode.alignedRaw s op frame.inst p a581 a236
  have am:(alignedRaw s op p).mems[p.memoryIndex]?=some (laidOutMemory p):=by
    rw[alignedRaw,mems_paid];exact laidOutRaw_memory s op p hm
  have size:=wp_size_guard cfg (fuel+386) (475*op+rest) (alignedRaw s op p) limits base.toArray aligned (caller::callers)
    tailCode (scratch p) p.size p.mi p.memoryIndex (laidOutMemory p) post
    (by simp[aligned,inner,outer,loadedFrame,reservedRawFrame,emptyBlockFrame,show 3<frame.locals.size by omega])
    ac.record.allocation.search.module hcode.record.allocation.search.memoryIndex am
    (by rw[shape.2.1,n.1];omega) words.1 hn.sizeSigned
    ((alignedRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[checkedRaw,checked,checkedRawFrame,alignedRawFrame,reservedRawFrame,aligned,inner,outer,enclosing,loadedFrame,emptyBlockFrame,tailCode,op] using choice)
  have lc:=hcode.laidOutRaw s op frame.inst p a581 a236
  have align:=wp_alignment_guard cfg (fuel+392) (6*op+(475*op+rest)) (laidOutRaw s op p) limits base.toArray inner (caller::callers)
    (WNear.Binary.StateDecodeRaw.sizeGuard++tailCode) (scratch p) p.mi p.memoryIndex (laidOutMemory p) post
    (by simp[inner,outer,reservedRawFrame,emptyBlockFrame,show 3<frame.locals.size by omega])
    lc.record.allocation.search.module hcode.record.allocation.search.memoryIndex (laidOutRaw_memory s op p hm)
    (by rw[shape.2.1,n.1];omega) words.2
    ((laidOutRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[alignedRaw,aligned,op] using size)
  let inside:=WNear.Binary.StateDecodeRaw.alignmentGuard++WNear.Binary.StateDecodeRaw.sizeGuard++tailCode
  have inBlock:=wp_block_empty cfg (fuel+397) (486*op+rest) (laidOutRaw s op p) limits base.toArray outer (caller::callers)
    inside panic844 post ((laidOutRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[inside,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 5*cfg.regularOpCost+(6*op+(475*op+rest))=486*op+rest by dsimp[op];omega] using align)
  have outBlock:=wp_block_empty cfg (fuel+398) (486*op+rest) (laidOutRaw s op p) limits base.toArray (reservedRawFrame frame p) (caller::callers)
    (.block .empty inside::panic844) (panic842++code) post ((laidOutRaw_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2) inBlock
  have first:=wp_raw_prefix cfg (fuel+399) (486*op+rest) s limits base frame (caller::callers)
    (.block .empty (.block .empty inside::panic844)::panic842++code) p post hn a581 a236 hcode h1 hs hm hg hv
    (by simp only[List.length_cons];omega) (hc.mono (by dsimp[op];omega)) outBlock
  simpa only[WNear.Binary.StateDecodeRaw.body767,rawFinish,tailCode,inside,panic842,panic844,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 87*cfg.regularOpCost+(486*op+rest)=573*cfg.regularOpCost+rest by dsimp[op];omega] using first
end WNear.Proofs.StateDecodeRaw
