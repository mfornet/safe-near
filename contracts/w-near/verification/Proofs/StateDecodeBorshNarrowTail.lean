import Proofs.StateDecodeBorshOutputWP
import Proofs.StateDecodeBorshGuardReadback
import Proofs.StateDecodeBorshLocals
import Proofs.StateDecodeBorshControl

/-! Actual425's fourth block, accepted narrow guard, vector/usage caches and
final output/branch/restore. The original domain supplies every resource. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] WP atCode narrowSaved narrowGuarded vectorSaved usageCached after
  savedNarrowMemory vectorHighMemory cachedMemory vectorLength vectorPacked usageValue
  readI32 readI64 writeI32 writeI64 wideHigh wideLow prefixPacked prefixLength savedWideMemory

def narrowTailFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)(height:Nat)(code:Expr):=
  emptyBlockFrame (emptyBlockFrame (emptyBlockFrame (wideFrame frame p q) height
    (WNear.Binary.StateDecodeBorsh.restore++code)) height WNear.Binary.StateDecodeBorsh.wideRejected)
    height WNear.Binary.StateDecodeBorsh.prefixRejected

private theorem cut_cost (n op rest : Nat) : (18*n+1377)*op+(57*op+rest)=(18*n+1434)*op+rest:=by simp only[Nat.add_mul];omega
private theorem cut_guard (n op rest : Nat) : (18*n+1382)*op+(52*op+rest)=(18*n+1434)*op+rest:=by simp only[Nat.add_mul];omega
private theorem cut_vector (n op rest : Nat) : (18*n+1398)*op+(36*op+rest)=(18*n+1434)*op+rest:=by simp only[Nat.add_mul];omega

private theorem cached_frame_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)(height:Nat)(code:Expr):
    cacheNarrowFrame
      (vectorCachedFrame (emptyBlockFrame (narrowTailFrame frame p q height code) height WNear.Binary.StateDecodeBorsh.narrowRejected)
        (savedNarrowMemory p q) (scratch p)) (cachedMemory p q) (scratch p)=
      exitNested (finalFrame frame p q) height code WNear.Binary.StateDecodeBorsh.wideRejected
        WNear.Binary.StateDecodeBorsh.prefixRejected WNear.Binary.StateDecodeBorsh.narrowRejected := by
  simp only[cacheNarrowFrame,vectorCachedFrame,vectorHighFrame,StateDecodeScalar.loaded64Frame,
    narrowTailFrame,emptyBlockFrame,exitNested,finalFrame,vectorFrame,vectorLength,vectorPacked,
    cacheVectorHighMemory,vectorHighMemory,usageValue]

private theorem vector_store_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    vectorCachedStore (narrowGuarded cfg s p q) cfg.regularOpCost p.memoryIndex (savedNarrowMemory p q) (scratch p)=vectorSaved cfg s p q:=by
  simp only[vectorCachedStore,vectorHighStore,vectorSaved,vectorHighSaved,cacheVectorHighMemory,vectorHighMemory,vectorLength,vectorPacked]

theorem wp_narrow_tail (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global425)
    (h0:frame.locals[0]?=some (.i32 p.out425))(h1:frame.locals[1]?=some (.i32 p.slice))(hs:8≤frame.locals.size)
    (hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+58) (.next (atCode (narrowSaved cfg s p q) limits base.toArray
      (narrowTailFrame frame p q base.toArray.size code) callers
      ([.block .empty WNear.Binary.StateDecodeBorsh.acceptedNarrow]++WNear.Binary.StateDecodeBorsh.narrowRejected)))
      (57*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=emptyBlockFrame (narrowTailFrame frame p q base.toArray.size code) base.toArray.size WNear.Binary.StateDecodeBorsh.narrowRejected
  let g:=vectorCachedFrame f (savedNarrowMemory p q) (scratch p)
  have wfLocals:=wide_locals frame p q hs h0 h1
  have f2:f.locals[2]?=some (.i32 (scratch p)):=by simpa only[f,narrowTailFrame,emptyBlockFrame] using wfLocals.2.2.1
  have g2:g.locals[2]?=some (.i32 (scratch p)):=by simp [g,vectorCachedFrame,vectorHighFrame,f2]
  have fInst:f.inst=frame.inst:=by simp only[f,narrowTailFrame,emptyBlockFrame,wideFrame_inst]
  have gInst:g.inst=frame.inst:=by simp only[g,vectorCachedFrame,vectorHighFrame,fInst]
  have n:=scratch_numbers p hn
  have shape:=savedNarrowMemory_spec p q hn hd
  have cachedShape:=cachedMemory_spec p q hn hd
  have narrowFields:=narrowSaved_fields cfg s p q
  have guardFields:=narrowGuarded_fields cfg s p q
  have vectorFields:=vectorSaved_fields cfg s p q
  have ns:(narrowSaved cfg s p q).host.gas.Credits (57*op+rest):=narrowSaved_credits cfg s p q hn hd _
    (by simpa only[bodyCost,op,cut_cost] using hc)
  have ng:(narrowGuarded cfg s p q).host.gas.Credits (52*op+rest):=narrowGuarded_credits cfg s p q hn hd _
    (by simpa only[bodyCost,op,cut_guard] using hc)
  have vs:(vectorSaved cfg s p q).host.gas.Credits (36*op+rest):=vectorSaved_credits cfg s p q hn hd _
    (by simpa only[bodyCost,op,cut_vector] using hc)
  have fl:=final_locals frame p q hs h0 h1
  have finalCode:Code s (finalFrame frame p q).inst p q a581 a236:=by simpa only[finalFrame_inst] using hcode
  have output:=wp_final_output cfg fuel rest s limits base.toArray (finalFrame frame p q) callers code
    WNear.Binary.StateDecodeBorsh.wideRejected WNear.Binary.StateDecodeBorsh.prefixRejected WNear.Binary.StateDecodeBorsh.narrowRejected []
    p q a581 a236 post hn hd finalCode hm hg fl.1 fl.2.2.1 fl.2.2.2.1 fl.2.2.2.2.2.1 fl.2.2.2.2.2.2.2.1 fl.2.2.2.2.2.2.1 fl.2.1 hc hnext
  let suffix:Expr:=WNear.Binary.StateDecodeBorsh.output++[.br 3]
  have outputNext:WP cfg (fuel+33) (.next (atCode (paid (vectorSaved cfg s p q) cfg.regularOpCost 3) limits base.toArray
      (cacheNarrowFrame g (cachedMemory p q) (scratch p)) callers suffix)) (33*op+rest) post:=by
    rw[cached_frame_eq frame p q base.toArray.size code]
    simpa only[usageCached,suffix,op,g,f] using output
  have vectorModule:(vectorSaved cfg s p q).modules[g.inst]?=some p.mi:=by
    rw[vectorFields.2.1,gInst];exact hcode.prefixCode.child.module
  have vectorMemory: (vectorSaved cfg s p q).mems[p.memoryIndex]?=some (cachedMemory p q):=vectorSaved_memory cfg s p q hn hd hm
  have nb:(scratch p).toNat+92≤(cachedMemory p q).byteSize:=by rw[cachedShape.2.1];omega
  have cache:=wp_cache_narrow cfg (fuel+33) (33*op+rest) (vectorSaved cfg s p q) limits base.toArray g callers suffix
    (scratch p) p.mi p.memoryIndex (cachedMemory p q) post g2 vectorModule hcode.prefixCode.child.memoryIndex vectorMemory nb
    (vs.mono (by dsimp[op];omega)) outputNext
  have cacheNext:WP cfg (fuel+36) (.next (atCode (vectorCachedStore (narrowGuarded cfg s p q) cfg.regularOpCost p.memoryIndex
      (savedNarrowMemory p q) (scratch p)) limits base.toArray g callers (WNear.Binary.StateDecodeBorsh.cacheNarrow++suffix))) (36*op+rest) post:=by
    rw[vector_store_eq]
    simpa only[show fuel+33+3=fuel+36 by omega,show 3*cfg.regularOpCost+(33*op+rest)=36*op+rest by dsimp[op];omega] using cache
  have guardModule:(narrowGuarded cfg s p q).modules[f.inst]?=some p.mi:=by
    rw[guardFields.2.1,fInst];exact hcode.prefixCode.child.module
  have guardMemory:(narrowGuarded cfg s p q).mems[p.memoryIndex]?=some (savedNarrowMemory p q):=narrowGuarded_memory cfg s p q hn hd hm
  have a24:((scratch p+16)+8).toNat=(scratch p).toNat+24:=by
    have eq:(scratch p+16)+8=scratch p+24:=by rw[UInt32.add_assoc];rfl
    rw[eq];exact scratch_add p hn 24 (by omega)
  have a8:(scratch p+8).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have bs:((scratch p+16)+8).toNat+4≤(savedNarrowMemory p q).byteSize:=by rw[a24,shape.2.1];omega
  have bh:(scratch p+8).toNat+4≤(savedNarrowMemory p q).byteSize:=by rw[a8,shape.2.1];omega
  have bl:(scratch p).toNat+24≤(savedNarrowMemory p q).byteSize:=by rw[shape.2.1];omega
  have vector:=wp_cache_vector cfg (fuel+36) (36*op+rest) (narrowGuarded cfg s p q) limits base.toArray f callers
    (WNear.Binary.StateDecodeBorsh.cacheNarrow++suffix) (scratch p) p.mi p.memoryIndex (savedNarrowMemory p q) post
    f2 guardModule hcode.prefixCode.child.memoryIndex guardMemory shape.1 bs bh bl
    (ng.mono (by dsimp[op];omega)) cacheNext
  have guardNext:WP cfg (fuel+52) (.next (atCode (paid (narrowSaved cfg s p q) cfg.regularOpCost 5) limits base.toArray f callers
      (WNear.Binary.StateDecodeBorsh.cacheVector++(WNear.Binary.StateDecodeBorsh.cacheNarrow++suffix)))) (52*op+rest) post:=by
    simpa only[narrowGuarded,show fuel+36+16=fuel+52 by omega,show 16*cfg.regularOpCost+(36*op+rest)=52*op+rest by dsimp[op];omega] using vector
  have narrowModule:(narrowSaved cfg s p q).modules[f.inst]?=some p.mi:=by
    rw[narrowFields.2.1,fInst];exact hcode.prefixCode.child.module
  have narrowMemory:(narrowSaved cfg s p q).mems[p.memoryIndex]?=some (savedNarrowMemory p q):=narrowSaved_memory cfg s p q hn hd hm
  have bound:(scratch p).toNat+60≤(savedNarrowMemory p q).byteSize:=by rw[shape.2.1];omega
  have tag:readI32 (savedNarrowMemory p q) ((scratch p).toNat+56)≠1:=by rw[savedNarrowMemory_tag p q hn hd];decide
  have guard:=wp_guard cfg (fuel+52) (52*op+rest) (narrowSaved cfg s p q) limits base.toArray f callers
    (WNear.Binary.StateDecodeBorsh.cacheVector++(WNear.Binary.StateDecodeBorsh.cacheNarrow++suffix)) 0 (scratch p)
    p.mi p.memoryIndex (savedNarrowMemory p q) post f2 narrowModule hcode.prefixCode.child.memoryIndex narrowMemory bound tag
    (ns.mono (by dsimp[op];omega)) guardNext
  have inside:WP cfg (fuel+57) (.next (atCode (narrowSaved cfg s p q) limits base.toArray f callers
      WNear.Binary.StateDecodeBorsh.acceptedNarrow)) (57*op+rest) post:=by
    simpa only[←narrow_guard_exact,WNear.Binary.StateDecodeBorsh.acceptedNarrow,suffix,List.append_assoc,
      show fuel+52+5=fuel+57 by omega,show 5*cfg.regularOpCost+(52*op+rest)=57*op+rest by dsimp[op];omega] using guard
  have block:=wp_block_empty cfg (fuel+57) (57*op+rest) (narrowSaved cfg s p q) limits base.toArray
    (narrowTailFrame frame p q base.toArray.size code) callers WNear.Binary.StateDecodeBorsh.acceptedNarrow WNear.Binary.StateDecodeBorsh.narrowRejected post ns inside
  simpa only[List.singleton_append,show fuel+57+1=fuel+58 by omega,op] using block
end WNear.Proofs.StateDecodeBorsh
