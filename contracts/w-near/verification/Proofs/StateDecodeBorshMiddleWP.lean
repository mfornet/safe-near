import Proofs.StateDecodeBorshSaveWP
import Proofs.StateDecodeBorshScalarCall
import Proofs.StateDecodeBorshControl
import Proofs.StateDecodeBorshCache
import Proofs.StateDecodeBorshGlobals
import Proofs.StateDecodeBorshLocals
import Proofs.StateDecodeBorshGuardReadback

/-! Opaque accepted425 middle: save the prefix, decode/save128 bits,
then decode/save64 bits. All three callee domains and current resources
are consequences of the original425 conditions. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode prefixSaved wideDecoded wideSaved wideGuarded wideCached narrowDecoded narrowSaved
  prefixMemory savedPrefixMemory wideMemory savedWideMemory narrowMemory narrowHighMemory savedNarrowMemory
  prefixFrame savedPrefixFrame wideFrame readI32 readI64 writeI32 writeI64

def middleCode:Expr:=WNear.Binary.StateDecodeBorsh.savePrefix++WNear.Binary.StateDecodeBorsh.scalarArguments++[.call 372]++
  WNear.Binary.StateDecodeBorsh.saveWide++WNear.Binary.StateDecodeBorsh.wideGuard++WNear.Binary.StateDecodeBorsh.cacheWide++
  WNear.Binary.StateDecodeBorsh.scalarArguments++[.call 371]++WNear.Binary.StateDecodeBorsh.saveNarrow
private theorem wide_call_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    ScalarCall.after true cfg (prefixSaved cfg s p q) p q=wideDecoded cfg s p q:=by
  unfold ScalarCall.after ScalarCall.layout wideDecoded wideArguments
  rfl
private theorem narrow_call_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    ScalarCall.after false cfg (wideCached cfg s p q) p q=narrowDecoded cfg s p q:=by
  unfold ScalarCall.after ScalarCall.layout narrowDecoded narrowArguments
  rfl

theorem wp_middle(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global425)
    (h0:frame.locals[0]?=some (.i32 p.out425))(h1:frame.locals[1]?=some (.i32 p.slice))(hs:8≤frame.locals.size)
    (hdepth:callers.length+2<limits.maxCallDepth)(hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (narrowSaved cfg s p q) limits base.toArray (wideFrame frame p q) callers code)) (57*cfg.regularOpCost+rest) post):
    WP cfg (fuel+321) (.next (atCode (prefixGuarded cfg s p q) limits base.toArray (prefixFrame frame p q) callers
      (middleCode++code))) (445*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have pl:=prefix_locals frame p q hs h0 h1
  have sl:=savedPrefix_locals frame p q hs h0 h1
  have wl:=wide_locals frame p q hs h0 h1
  have n:=scratch_numbers p hn
  let cN:=WNear.Binary.StateDecodeBorsh.saveNarrow++code
  have sn:=wp_narrow_save cfg fuel rest s limits base.toArray (wideFrame frame p q) callers code p q a581 a236 post hn hd
    (by simpa using hcode) hm wl.2.2.1 hc hnext
  have fc:=wideCached_fields cfg s p q
  have cc:Code (wideCached cfg s p q) (wideFrame frame p q).inst p q a581 a236:=by
    rw[wideFrame_inst]
    exact hcode.transport s (wideCached cfg s p q) frame.inst p q a581 a236 fc.1 fc.2.1 fc.2.2
  have cg:(wideCached cfg s p q).globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)}:=by
    rw[wideCached_globals cfg s p q hn hd hg]
    exact reserved_global s op p hg
  have cn:=ScalarCall.wp_call false cfg (fuel+16) (73*op+rest) (wideCached cfg s p q) limits base (wideFrame frame p q) callers cN p q a581 a236 post hn hd cc
    (wideCached_memory cfg s p q hn hd hm) cg wl.2.1 wl.2.2.1 hdepth
    ((wideCached_credits cfg s p q hn hd (228*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by simp only[Bool.false_eq_true,ite_false];dsimp[op];omega))
    (by rw[narrow_call_eq];simpa only[cN,op] using sn)
  let cC:=WNear.Binary.StateDecodeBorsh.scalarArguments++[.call 371]++cN
  have shape:=savedWideMemory_specs p q hn hd
  have a44:((scratch p+32)+12).toNat+8≤(savedWideMemory p q).byteSize:=by
    have a:((scratch p+32)+12).toNat=(scratch p).toNat+44:=by
      rw[UInt32.add_assoc];exact scratch_add p hn 44 (by omega)
    rw[a,shape.2.2.2.2.2.1];omega
  have ca:=wp_cache_wide cfg (fuel+138) (228*op+rest) (wideGuarded cfg s p q) limits base.toArray (savedPrefixFrame frame p q) callers cC
    (scratch p) p.mi p.memoryIndex (savedWideMemory p q) post sl.2.2.1
    (by rw[savedPrefixFrame_inst,(wideGuarded_fields cfg s p q).2.1];exact hcode.prefixCode.child.module)
    hcode.prefixCode.child.memoryIndex (wideGuarded_memory cfg s p q hn hd hm) a44 (by rw[shape.2.2.2.2.2.1];omega)
    ((wideGuarded_credits cfg s p q hn hd (238*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by omega))
    (by rw[cacheWideFrame_eq];simpa only[cC,wideCached,op,Bool.false_eq_true,ite_false,Nat.add_assoc,Nat.reduceAdd,show 155*cfg.regularOpCost+(73*cfg.regularOpCost+rest)=228*cfg.regularOpCost+rest by omega] using cn)
  let cG:=WNear.Binary.StateDecodeBorsh.cacheWide++cC
  have tag:=savedWideMemory_tag p q hn hd
  have guard:=wp_guard cfg (fuel+148) (238*op+rest) (wideSaved cfg s p q) limits base.toArray (savedPrefixFrame frame p q) callers cG 1
    (scratch p) p.mi p.memoryIndex (savedWideMemory p q) post sl.2.2.1
    (by rw[savedPrefixFrame_inst,(wideSaved_fields cfg s p q).2.1];exact hcode.prefixCode.child.module)
    hcode.prefixCode.child.memoryIndex (wideSaved_memory cfg s p q hn hd hm) (by rw[shape.2.2.2.2.2.1];omega)
    (by rw[tag];decide)
    ((wideSaved_credits cfg s p q hn hd (243*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by omega))
    (by simpa only[cG,wideGuarded,op,Nat.add_assoc,Nat.reduceAdd,show 10*cfg.regularOpCost+(228*cfg.regularOpCost+rest)=238*cfg.regularOpCost+rest by omega] using ca)
  let cW:=WNear.Binary.StateDecodeBorsh.wideGuard++cG
  have sw:=wp_wide_save cfg (fuel+153) rest s limits base.toArray (savedPrefixFrame frame p q) callers cW p q a581 a236 post hn hd
    (by simpa using hcode) hm sl.2.2.1 sl.2.2.2.2.1 hc
    (by simpa only[cW,wide_guard_exact,op,Nat.add_assoc,Nat.reduceAdd,show 5*cfg.regularOpCost+(238*cfg.regularOpCost+rest)=243*cfg.regularOpCost+rest by omega] using guard)
  have fs:=prefixSaved_fields cfg s p q
  have cs:Code (prefixSaved cfg s p q) (savedPrefixFrame frame p q).inst p q a581 a236:=by
    rw[savedPrefixFrame_inst]
    exact hcode.transport s (prefixSaved cfg s p q) frame.inst p q a581 a236 fs.1 fs.2.1 fs.2.2
  have gs:=prefixSaved_global cfg s p q hn hd hg
  let cS:=WNear.Binary.StateDecodeBorsh.saveWide++cW
  have cw:=ScalarCall.wp_call true cfg (fuel+173) (263*op+rest) (prefixSaved cfg s p q) limits base (savedPrefixFrame frame p q) callers cS p q a581 a236 post hn hd cs
    (prefixSaved_memory cfg s p q hn hd hm) gs sl.2.1 sl.2.2.1 hdepth
    ((prefixSaved_credits cfg s p q hn hd (435*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by simp only[ite_true];dsimp[op];omega))
    (by rw[wide_call_eq];simpa only[cS,op] using sw)
  let cP:=WNear.Binary.StateDecodeBorsh.scalarArguments++[.call 372]++cS
  have sp:=wp_prefix_save cfg (fuel+311) rest s limits base.toArray (prefixFrame frame p q) callers cP p q a581 a236 post hn hd
    (by simpa using hcode) hm pl.2.2.1 pl.2.2.2.1 hc
    (by rw[prefixSavedFrame_eq];simpa only[cP,op,ite_true,Nat.add_assoc,Nat.reduceAdd,show 172*cfg.regularOpCost+(263*cfg.regularOpCost+rest)=435*cfg.regularOpCost+rest by omega] using cw)
  simpa only[middleCode,cP,cS,cW,cG,cC,cN,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using sp
end WNear.Proofs.StateDecodeBorsh
