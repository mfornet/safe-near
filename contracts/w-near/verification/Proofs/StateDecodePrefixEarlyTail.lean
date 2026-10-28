import Proofs.StateDecodePrefixEarlyHead
import Proofs.StateDecodePrefixPayloadCall
import Proofs.StateDecodePrefixLengthStatus
import Proofs.StateDecodePrefixEarlyReadback

/-! Actual316 continues from its accepted word through the second real slice
borrow, retaining the sequential slice mutation and all enclosing labels. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
private theorem enough_inst (f : CallFrame) (m : Memory) (a b : UInt32) : (enoughFrame f m a b).inst=f.inst:=rfl
private theorem count_inst (f : CallFrame) (a : UInt32) : (countFrame f a).inst=f.inst:=rfl
attribute [local irreducible] enoughFrame countFrame
attribute [local irreducible] WP atCode statusPrefix droppedPrefix advancedPrefix countedPrefix lengthPrefix lengthCheckedPrefix enoughPrefix payloadPrefix takenFourMemory droppedFourMemory advancedMemory lengthMemory

theorem wp_early_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (h1 : frame.locals[1]?=some (.i32 p.slice)) (hs : 6≤frame.locals.size)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (183*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (payloadPrefix cfg s p) limits base.toArray
      (enoughPrefixFrame (prefixLabels frame base.toArray.size code) p) callers payloadRest)) rest post) :
    WP cfg (fuel+82) (.next (atCode (statusPrefix cfg s p) limits base.toArray
      (statusPrefixFrame (prefixLabels frame base.toArray.size code) p) callers earlyRest))
      (106*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:=statusPrefixFrame (prefixLabels frame base.toArray.size code) p
  let c:=countFrame f (count p)
  let e:=enoughFrame c (lengthMemory p) p.slice (scratch p)
  have hs':6≤(prefixLabels frame base.toArray.size code).locals.size:=hs
  have fl:=statusPrefixFrame_locals (prefixLabels frame base.toArray.size code) p hs'
  have cl:=countedPrefixFrame_locals (prefixLabels frame base.toArray.size code) p hs'
  have el:=enoughPrefixFrame_locals (prefixLabels frame base.toArray.size code) p hs' hn
  have f1:f.locals[1]?=some (.i32 p.slice):=fl.2.2.1.trans h1
  have f2:f.locals[2]?=some (.i32 (scratch p)):=fl.2.2.2.1
  have f4:f.locals[4]?=some (.i64 (StateDecodePrefixLeaves.packedWord (count p))):=fl.2.2.2.2.2
  have c1:c.locals[1]?=some (.i32 p.slice):=cl.2.2.1.trans h1
  have c2:c.locals[2]?=some (.i32 (scratch p)):=cl.2.2.2.1
  have c3:c.locals[3]?=some (.i32 (count p)):=cl.2.2.2.2.1
  have e1:e.locals[1]?=some (.i32 p.slice):=el.2.2.1.trans h1
  have e2:e.locals[2]?=some (.i32 (scratch p)):=el.2.2.2.1
  have e3:e.locals[3]?=some (.i32 (count p)):=el.2.2.2.2.1
  have e5:e.locals[5]?=some (.i32 (remaining p)):=el.2.2.2.2.2.2
  have se:=scratch_end p hn
  have sb:=hn.spBound
  have pn:=payload_numbers p hn
  have ls:=lengthMemory_spec p hn
  have ds:=droppedFour_spec p hn
  have ts:=takenFour_spec p hn
  have a16:(scratch p+16).toNat=(scratch p).toNat+16:=scratch_add p hn 16 (by omega)
  have a24:(scratch p+24).toNat=(scratch p).toNat+24:=scratch_add p hn 24 (by omega)
  have a32:(scratch p+32).toNat=(scratch p).toNat+32:=scratch_add p hn 32 (by omega)
  have fi:f.inst=frame.inst:=by simp only[f,statusPrefixFrame,statusFrame,guardedPrefixFrame,AllocateVector.loadedFrame,reservedPrefixFrame,prefixLabels,emptyBlockFrame]
  have ci:c.inst=frame.inst:=(count_inst f (count p)).trans fi
  have ei:e.inst=frame.inst:=(enough_inst c (lengthMemory p) p.slice (scratch p)).trans ci
  have pf:=enoughPrefix_fields cfg s p
  have payload:=wp_payload_call cfg fuel rest (enoughPrefix cfg s p) limits base e callers payloadRest
    (scratch p) p.slice (payloadPointer p) (remaining p) (count p) p.mi p.memoryIndex p.takeAddress (lengthMemory p) post
    e1 e2 e5 e3 (by rw[pf.2.1,ei];exact hcode.module) hcode.memoryIndex (enoughPrefix_memory cfg s p hm hn)
    hcode.takeAddress (by rw[pf.1,ei];exact hcode.takeFunction) ls.1 (by rw[ls.2.1];have h:=hn.sliceBound;omega)
    (by rw[a16,ls.2.1];omega) (length_slice_low p hn) pn.2.2.1 hd
    ((enoughPrefix_gas cfg s p _ (hc.mono (by omega))).2.2)
    (by simpa only[payloadPrefix,payloadAfter,takePayloadOut,e,c,f,enoughPrefixFrame,countedPrefixFrame] using hnext)
  have ef:=lengthCheckedPrefix_fields cfg s p
  have enough:=wp_enough cfg (fuel+21) (30*op+rest) (lengthCheckedPrefix cfg s p) limits base.toArray c callers
    (WNear.Binary.StateDecodePrefix.takePayload++payloadRest) p.slice (scratch p) p.mi p.memoryIndex (lengthMemory p) post
    c1 c2 (by rw[ef.2.1,ci];exact hcode.module) hcode.memoryIndex (lengthCheckedPrefix_memory cfg s p hm hn)
    (by rw[ls.2.1];exact hn.sliceBound) (by rw[ls.2.1];omega)
    (by rw[(enough_reads p hn).1,(enough_reads p hn).2];exact pn.2.2.1)
    ((lengthCheckedPrefix_gas cfg s p _ (hc.mono (by simp only[op];omega))).2.2)
    (by simpa only[enoughPrefix,e,op] using payload)
  have lf:=lengthPrefix_fields cfg s p
  have lw:=length_words p hn
  have status:=wp_length_status cfg (fuel+30) (38*op+rest) (lengthPrefix cfg s p) limits base.toArray c callers
    (.block .empty WNear.Binary.StateDecodePrefix.enough::WNear.Binary.StateDecodePrefix.takePayload++payloadRest)
    (scratch p) p.mi p.memoryIndex (lengthMemory p) post c2
    (by rw[lf.2.1,ci];exact hcode.module) hcode.memoryIndex (lengthPrefix_memory cfg s p hm hn)
    (by rw[ls.2.1];omega)
    (by simpa only[lengthOut,a24] using lw.1)
    ((lengthPrefix_gas cfg s p _ (hc.mono (by simp only[op];omega))).2.2)
    (by simpa only[lengthCheckedPrefix,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 8*cfg.regularOpCost+(30*op+rest)=38*op+rest by simp only[op];omega] using enough)
  have af:=countedPrefix_fields cfg s p
  have ash:=advancedMemory_spec p hn
  have length:=wp_length_call cfg (fuel+33) (41*op+rest) (countedPrefix cfg s p) limits base c callers
    (WNear.Binary.StateDecodePrefix.lengthStatus++.block .empty WNear.Binary.StateDecodePrefix.enough::WNear.Binary.StateDecodePrefix.takePayload++payloadRest)
    (scratch p) (count p) p.mi p.memoryIndex p.lengthAddress (advancedMemory p) post c2 c3
    (by rw[af.2.1,ci];exact hcode.module) hcode.memoryIndex (countedPrefix_memory cfg s p hm hn)
    hcode.lengthAddress (by rw[af.1,ci];exact hcode.lengthFunction) ash.1 (by rw[a24,ash.2.1];omega) hd
    ((countedPrefix_gas cfg s p _ (hc.mono (by simp only[op];omega))).2.2)
    (by simpa only[lengthPrefix,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 3*cfg.regularOpCost+(38*op+rest)=41*op+rest by simp only[op];omega] using status)
  have nonzero:=wp_nonzero_count cfg (fuel+45) (61*op+rest) (advancedPrefix cfg s p) limits base.toArray f callers
    (WNear.Binary.StateDecodePrefix.lengthArguments++WNear.Binary.StateDecodePrefix.lengthStatus++
      [.block .empty WNear.Binary.StateDecodePrefix.enough]++WNear.Binary.StateDecodePrefix.takePayload++payloadRest)
    (count p) post f4 hn.countPositive ((advancedPrefix_gas cfg s p _ (hc.mono (by simp only[op];omega))).2.2)
    (by simpa only[countedPrefix,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append,Nat.add_assoc,Nat.reduceAdd,
      show 20*cfg.regularOpCost+(41*op+rest)=61*op+rest by simp only[op];omega] using length)
  have df:=droppedPrefix_fields cfg s p
  have advance:=wp_advance_four cfg (fuel+52) (67*op+rest) (droppedPrefix cfg s p) limits base.toArray f callers
    (.block .empty WNear.Binary.StateDecodePrefix.nonzero::WNear.Binary.StateDecodePrefix.lengthArguments++
      WNear.Binary.StateDecodePrefix.lengthStatus++[.block .empty WNear.Binary.StateDecodePrefix.enough]++
      WNear.Binary.StateDecodePrefix.takePayload++payloadRest)
    (scratch p) p.slice p.mi p.memoryIndex (droppedFourMemory p) post f1 f2
    (by rw[df.2.1,fi];exact hcode.module) hcode.memoryIndex (droppedPrefix_memory cfg s p hm)
    (by rw[ds.2.1];omega) (by rw[ds.2.1];exact hn.sliceBound)
    ((droppedPrefix_gas cfg s p _ (hc.mono (by simp only[op];omega))).2.2)
    (by simpa only[advancedPrefix,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 6*cfg.regularOpCost+(61*op+rest)=67*op+rest by simp only[op];omega] using nonzero)
  have sf:=statusPrefix_fields cfg s p
  have drop:=wp_drop_four_call cfg (fuel+56) (71*op+rest) (statusPrefix cfg s p) limits base f callers
    (WNear.Binary.StateDecodePrefix.advanceFour++.block .empty WNear.Binary.StateDecodePrefix.nonzero::
      WNear.Binary.StateDecodePrefix.lengthArguments++WNear.Binary.StateDecodePrefix.lengthStatus++
      [.block .empty WNear.Binary.StateDecodePrefix.enough]++WNear.Binary.StateDecodePrefix.takePayload++payloadRest)
    (scratch p) p.slice p.pointer p.length p.mi p.memoryIndex p.dropAddress (takenFourMemory p) post f1 f2
    (by rw[sf.2.1,fi];exact hcode.module) hcode.memoryIndex (statusPrefix_memory cfg s p hm)
    hcode.dropAddress (by rw[sf.1,fi];exact hcode.dropFunction) ts.1 (by rw[ts.2.1];exact hn.sliceBound)
    (by rw[a32,ts.2.1];omega) (taken_slice_low p hn) (taken_slice_high p hn) pn.2.2.2.1 hd
    ((statusPrefix_gas cfg s p _ (hc.mono (by simp only[op];omega))).2.2)
    (by simpa only[droppedPrefix,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append,Nat.add_assoc,Nat.reduceAdd,
      show 4*cfg.regularOpCost+(67*op+rest)=71*op+rest by simp only[op];omega] using advance)
  simpa only[earlyRest,List.append_assoc,List.cons_append,List.nil_append,List.singleton_append,Nat.add_assoc,Nat.reduceAdd,
    show 35*cfg.regularOpCost+(71*op+rest)=106*cfg.regularOpCost+rest by simp only[op];omega] using drop
end WNear.Proofs.StateDecodePrefix
