import Proofs.StateDecodePrefixSetup
import Proofs.StateDecodePrefixEarlyGas
import Proofs.StateDecodePrefixEarlyFrame
import Proofs.StateDecodePrefixEarlyMemory
import Proofs.StateDecodePrefixEarlyLocals

/-! The actual316 head executes all initial blocks and both deployed helpers;
its continuation begins after the real packed-word status check. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open AllocateVector (loadedFrame)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode reservedPrefix guardedPrefix takenPrefix wordPrefix statusPrefix takenFourMemory

def earlyRest : Expr := WNear.Binary.StateDecodePrefix.dropFour++WNear.Binary.StateDecodePrefix.advanceFour++
  [.block .empty WNear.Binary.StateDecodePrefix.nonzero]++WNear.Binary.StateDecodePrefix.lengthArguments++
  WNear.Binary.StateDecodePrefix.lengthStatus++[.block .empty WNear.Binary.StateDecodePrefix.enough]++
  WNear.Binary.StateDecodePrefix.takePayload++payloadRest

theorem wp_early_head (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global)
    (hv : p.global.value=.i32 p.sp) (h1 : frame.locals[1]?=some (.i32 p.slice)) (hs : 6≤frame.locals.size)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (77*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (statusPrefix cfg s p) limits base.toArray
      (statusPrefixFrame (prefixLabels frame base.toArray.size code) p) callers earlyRest)) rest post) :
    WP cfg (fuel+67) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.body++code)))
      (77*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let outer:=emptyBlockFrame (reservedPrefixFrame frame p) base.toArray.size (WNear.Binary.StateDecodePrefix.restore++code)
  let middle:=emptyBlockFrame outer base.toArray.size WNear.Binary.StateDecodePrefix.invalid
  let inner:=emptyBlockFrame middle base.toArray.size WNear.Binary.StateDecodePrefix.short
  let guarded:=loadedFrame inner 3 p.length
  let accepted:=emptyBlockFrame guarded base.toArray.size WNear.Binary.StateDecodePrefix.panic
  let tail:=WNear.Binary.StateDecodePrefix.wordStatus++earlyRest
  have se:=scratch_end p hn
  have sb:=hn.spBound
  have pn:=payload_numbers p hn
  have shape:=takenFour_spec p hn
  have takenWords:=takenFour_words p hn
  have outNat : (takeFourOut p).toNat=(scratch p).toNat+40:=scratch_add p hn 40 (by omega)
  have g1:guarded.locals[1]?=some (.i32 p.slice):=by simp[guarded,inner,middle,outer,loadedFrame,reservedPrefixFrame,emptyBlockFrame,h1]
  have g2:guarded.locals[2]?=some (.i32 (scratch p)):=by simp[guarded,inner,middle,outer,loadedFrame,reservedPrefixFrame,emptyBlockFrame,show 2<frame.locals.size by omega]
  have g3:guarded.locals[3]?=some (.i32 p.length):=by simp[guarded,loadedFrame,inner,middle,outer,reservedPrefixFrame,emptyBlockFrame,show 3<frame.locals.size by omega]
  have status:=wp_word_status cfg fuel rest (wordPrefix cfg s p) limits base.toArray accepted callers earlyRest (count p) post
    ((wordPrefix_gas cfg s p _ (hc.mono (by omega))).2.2)
    (by simpa only[statusPrefix,statusPrefixFrame,guardedPrefixFrame,reservedPrefixFrame,prefixLabels,accepted,guarded,inner,middle,outer,statusFrame,loadedFrame,emptyBlockFrame] using hnext)
  have wordFields:=takenPrefix_fields cfg s p
  have word:=wp_prefix_word_call cfg (fuel+6) (6*op+rest) (takenPrefix cfg s p) limits base accepted callers tail
    (scratch p) p.pointer p.mi p.memoryIndex p.wordAddress (takenFourMemory p) post g2
    (by rw[wordFields.2.1];exact hcode.module) hcode.memoryIndex (takenPrefix_memory cfg s p hm)
    hcode.wordAddress (by rw[wordFields.1];exact hcode.wordFunction)
    (by rw[shape.2.1];omega)
    (by rw[←outNat];exact takenWords.1)
    (by have h:=takenWords.2;rw[outNat] at h;simpa only[Nat.add_assoc,Nat.reduceAdd] using h)
    (by rw[shape.2.1];have hb:=hn.payloadBound;omega) hd
    ((takenPrefix_gas cfg s p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by
      have arr:(base++[Value.i64 (StateDecodePrefixLeaves.packedWord (readI32 (takenFourMemory p) p.pointer.toNat))]).toArray=
        base.toArray.push (.i64 (StateDecodePrefixLeaves.packedWord (count p))):=by
        rw[count_after_take p hn];apply Array.toList_inj.mp;simp
      simpa only[wordPrefix,arr,tail,op] using status)
  have acceptBlock:=wp_block_empty cfg (fuel+31) (36*op+rest) (takenPrefix cfg s p) limits base.toArray guarded callers
    WNear.Binary.StateDecodePrefix.accepted WNear.Binary.StateDecodePrefix.panic post
    ((takenPrefix_gas cfg s p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[WNear.Binary.StateDecodePrefix.accepted,tail,earlyRest,payloadRest,accepted,List.append_assoc,
      show 30*cfg.regularOpCost+(6*op+rest)=36*op+rest by dsimp[op];omega] using word)
  have guardFields:=guardedPrefix_fields cfg s p
  have take:=wp_take_call cfg (fuel+32) (36*op+rest) (guardedPrefix s op p) limits base guarded callers
    ([.block .empty WNear.Binary.StateDecodePrefix.accepted]++WNear.Binary.StateDecodePrefix.panic) (scratch p) p.slice p.pointer p.length
    p.mi p.memoryIndex p.takeAddress p.memory post g1 g2 g3
    (by rw[guardFields.2.1];exact hcode.module) hcode.memoryIndex (guardedPrefix_memory cfg s p hm)
    hcode.takeAddress (by rw[guardFields.1];exact hcode.takeFunction) hn.wf (by have hb:=hn.sliceBound;omega)
    (by change (takeFourOut p).toNat+8≤p.memory.byteSize;rw[outNat];omega) hn.pointerRead pn.2.2.2.1 hd
    ((guardedPrefix_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[takenPrefix,takeFourOut,op,List.singleton_append] using acceptBlock)
  have rc:Code (reservedPrefix s op p) frame.inst p:=by
    apply hcode.transport s (reservedPrefix s op p) frame.inst p
    · simp only[reservedPrefix,setGlobal,StorePairCaller.paid,chargedStore]
    · simp only[reservedPrefix,setGlobal,StorePairCaller.paid,chargedStore]
  have rmem:(reservedPrefix s op p).mems[p.memoryIndex]?=some p.memory:=by
    simpa only[reservedPrefix,setGlobal,StorePairCaller.paid,chargedStore] using hm
  have guard:=wp_length_guard cfg (fuel+53) (66*op+rest) (reservedPrefix s op p) limits base.toArray inner callers
    (WNear.Binary.StateDecodePrefix.takeFour++[.block .empty WNear.Binary.StateDecodePrefix.accepted]++WNear.Binary.StateDecodePrefix.panic)
    p.slice p.mi p.memoryIndex p.memory post
    (by simp[inner,middle,outer,reservedPrefixFrame,emptyBlockFrame,h1])
    rc.module hcode.memoryIndex rmem hn.sliceBound (by rw[hn.lengthRead];exact pn.2.2.2.1)
    ((reservedPrefix_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[guardedPrefix,guarded,hn.lengthRead,op,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 30*cfg.regularOpCost+(36*op+rest)=66*op+rest by dsimp[op];omega] using take)
  let innerBody:=WNear.Binary.StateDecodePrefix.lengthGuard++WNear.Binary.StateDecodePrefix.takeFour++
    [.block .empty WNear.Binary.StateDecodePrefix.accepted]++WNear.Binary.StateDecodePrefix.panic
  have innerBlock:=wp_block_empty cfg (fuel+59) (72*op+rest) (reservedPrefix s op p) limits base.toArray middle callers
    innerBody WNear.Binary.StateDecodePrefix.short post ((reservedPrefix_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2)
    (by simpa only[innerBody,List.append_assoc,show 6*cfg.regularOpCost+(66*op+rest)=72*op+rest by dsimp[op];omega] using guard)
  have middleBlock:=wp_block_empty cfg (fuel+60) (72*op+rest) (reservedPrefix s op p) limits base.toArray outer callers
    (.block .empty innerBody::WNear.Binary.StateDecodePrefix.short) WNear.Binary.StateDecodePrefix.invalid post
    ((reservedPrefix_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2) innerBlock
  have outerBlock:=wp_block_empty cfg (fuel+61) (72*op+rest) (reservedPrefix s op p) limits base.toArray (reservedPrefixFrame frame p) callers
    (.block .empty (.block .empty innerBody::WNear.Binary.StateDecodePrefix.short)::WNear.Binary.StateDecodePrefix.invalid)
    (WNear.Binary.StateDecodePrefix.restore++code) post ((reservedPrefix_gas s op p _ (hc.mono (by dsimp[op];omega))).2.2) middleBlock
  have setup:=wp_prefix_setup cfg (fuel+62) (72*op+rest) s limits base.toArray frame callers
    (.block .empty (.block .empty (.block .empty innerBody::WNear.Binary.StateDecodePrefix.short)::WNear.Binary.StateDecodePrefix.invalid)::WNear.Binary.StateDecodePrefix.restore++code)
    p post hcode hg hv (hc.mono (by dsimp[op];omega)) outerBlock
  simpa only[WNear.Binary.StateDecodePrefix.body,innerBody,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 5*cfg.regularOpCost+(72*op+rest)=77*cfg.regularOpCost+rest by dsimp[op];omega] using setup
end WNear.Proofs.StateDecodePrefix
