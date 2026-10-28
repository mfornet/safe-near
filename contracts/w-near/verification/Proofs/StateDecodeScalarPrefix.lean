import Proofs.StateDecodeScalarSetupWP
import Proofs.StateDecodeScalarTakeCall
import Proofs.StateDecodeScalarWordCall
import Proofs.StateDecodeScalarStatus
import Proofs.StateDecodeScalarCode
import Proofs.StateDecodeScalarMemory
import Proofs.StateDecodeScalarCredits

/-! The deployed scalar prefix reserves its scratch frame, enters the real
three blocks, checks length, takes the slice, and decodes its accepted words. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

def successTail (wide : Bool) : Expr := WNear.Binary.StateDecodeScalar.cache wide++
  WNear.Binary.StateDecodeScalar.dropArguments wide++WNear.Binary.StateDecodeScalar.dropCache wide++
  WNear.Binary.StateDecodeScalar.outputValues wide++WNear.Binary.StateDecodeScalar.updateSlice wide

def acceptedFrame (wide : Bool) (frame : CallFrame) (p : Layout) (height : Nat) (code : Expr) :=
  emptyBlockFrame (emptyBlockFrame (guardedFrame frame p) height
    (WNear.Binary.StateDecodeScalar.invalid wide++code)) height WNear.Binary.StateDecodeScalar.finish

private theorem paid_memory (s : Store NearState) (op n i : Nat) : (paid s op n).mems[i]?=s.mems[i]? := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_module (s : Store NearState) (op n i : Nat) : (paid s op n).modules[i]?=s.modules[i]? := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem reserved_memory (s : Store NearState) (op : Nat) (p : Layout) :
    (reserved s op p).mems[p.memoryIndex]?=s.mems[p.memoryIndex]? := by
  unfold reserved
  exact paid_memory s op 5 p.memoryIndex

private theorem guarded_slots (frame : CallFrame) (p : Layout)
    (h1 : frame.locals[1]?=some (.i32 p.slice)) (hs : 4≤frame.locals.size) :
    (guardedFrame frame p).locals[1]?=some (.i32 p.slice) ∧
    (guardedFrame frame p).locals[2]?=some (.i32 (scratch p)) ∧
    (guardedFrame frame p).locals[3]?=some (.i32 p.length) := by
  simp [guardedFrame,reservedFrame,Array.set!,h1,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega]

private theorem cut_read (wide : Bool) (op rest : Nat) :
    (if wide then 82 else 74)*op+(5*op+rest)≤(if wide then 87 else 79)*op+rest := by
  cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
private theorem cut_taken (wide : Bool) (op rest : Nat) :
    41*op+((if wide then 46 else 38)*op+rest)≤(if wide then 87 else 79)*op+rest := by
  cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
private theorem word_offset (wide : Bool) : (WNear.Binary.StateDecodeScalar.wordOffset wide).toNat=(if wide then 16 else 24) := by cases wide <;> rfl
private theorem take_offset (wide : Bool) : (WNear.Binary.StateDecodeScalar.takeOffset wide).toNat=(if wide then 8 else 16) := by cases wide <;> rfl

attribute [local irreducible] WP atCode reserved guarded takeArguments taken wordArguments readWords accepted
  StateDecodeWords.callAfter StateDecodeSlices.callAfter takeAfter wordAfter

/-- Complete accepted prefix; its continuation runs inside the two remaining
actual block labels. All domain and installation hypotheses concern the input. -/
theorem wp_prefix (wide : Bool) (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post)
    (hn : Native wide p) (hcode : Code wide s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (h1 : frame.locals[1]?=some (.i32 p.slice)) (hs : 4≤frame.locals.size)
    (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((if wide then 87 else 79)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (accepted wide cfg s p) limits base.toArray
      (acceptedFrame wide frame p base.length code) callers (successTail wide))) rest post) :
    WP cfg (fuel+(if wide then 74 else 66)) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodeScalar.body wide++code)))
      ((if wide then 87 else 79)*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let af:=acceptedFrame wide frame p base.length code
  let outer:=emptyBlockFrame (reservedFrame frame p) base.length (WNear.Binary.StateDecodeScalar.invalid wide++code)
  let inner:=emptyBlockFrame outer base.length WNear.Binary.StateDecodeScalar.finish
  have slots:=guarded_slots frame p h1 hs
  have af2 : af.locals[2]?=some (.i32 (scratch p)) := slots.2.1
  have af1 : af.locals[1]?=some (.i32 p.slice) := slots.1
  have af3 : af.locals[3]?=some (.i32 p.length) := slots.2.2
  have inst : af.inst=frame.inst:=rfl
  have span:=scratch_spans wide p hn
  have endS:=scratch_end wide p hn
  have takeNat:=takeOut_nat wide p hn
  have wordNat:=wordOut_nat wide p hn
  have wt:=takenMemory_spec wide p hn
  have ww:=wordMemory_spec wide p hn
  have takenCode:=hcode.taken wide s op frame.inst p
  have readCode:=hcode.readWords wide cfg s frame.inst p
  have statusBound : (scratch p).toNat+(WNear.Binary.StateDecodeScalar.wordOffset wide).toNat+1≤(wordMemory wide p).byteSize := by
    rw [ww.2.1,word_offset,←wordNat]
    have h:=Nat.le_trans span.2.1 hn.spBound
    omega
  have statusZero : (wordMemory wide p).read8 ((scratch p).toNat+(WNear.Binary.StateDecodeScalar.wordOffset wide).toNat)=0 := by
    rw [word_offset,←wordNat]
    exact word_status wide p hn
  have cRead := readWords_credits wide cfg s p (5*op+rest) (hc.mono (cut_read wide op rest))
  have status := wp_status_guard cfg fuel rest (readWords wide cfg s p) limits base.toArray af callers
    (successTail wide) wide (scratch p) p.mi p.memoryIndex (wordMemory wide p) post af2
    (by rw [inst];exact readCode.module) hcode.memoryIndex (readWords_memory wide cfg s p hm)
    statusBound statusZero cRead (by simpa only [accepted,af,op] using hnext)
  have wordCost : StateDecodeWords.bodyCost wide+18=if wide then 41 else 33 := by cases wide <;> rfl
  have wordSteps : StateDecodeWords.bodySteps wide+9=if wide then 34 else 26 := by cases wide <;> rfl
  have cTaken := taken_credits wide cfg s p ((if wide then 46 else 38)*op+rest) (hc.mono (cut_taken wide op rest))
  have takeWords:=taken_words wide p hn
  have wordInputBound : (scratch p).toNat+(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+8≤(takenMemory wide p).byteSize := by
    rw [wt.2.1,take_offset,←takeNat]
    exact Nat.le_trans span.1 hn.spBound
  have wordOutputBound : (scratch p+WNear.Binary.StateDecodeScalar.wordOffset wide).toNat+(StateDecodeWords.widthNat wide+1)≤(takenMemory wide p).byteSize := by
    change (wordOut wide p).toNat+_≤_
    rw [wt.2.1]
    exact Nat.le_trans span.2.1 hn.spBound
  have wordSourceBound : p.pointer.toNat+StateDecodeWords.widthNat wide≤(takenMemory wide p).byteSize := by
    rw [wt.2.1]
    exact hn.payloadBound
  have takeRead : readI32 (takenMemory wide p) ((scratch p).toNat+(WNear.Binary.StateDecodeScalar.takeOffset wide).toNat)=p.pointer := by
    rw [take_offset,←takeNat]
    exact takeWords.1
  have takeLen : readI32 (takenMemory wide p) ((scratch p).toNat+((WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+4))=StateDecodeWords.width wide := by
    rw [take_offset,←Nat.add_assoc,←takeNat]
    exact takeWords.2
  have word := wp_word_call cfg (fuel+5) (5*op+rest) (taken wide s op p) limits base af callers
    (WNear.Binary.StateDecodeScalar.statusGuard wide++successTail wide) wide (scratch p) p.pointer p.mi p.memoryIndex p.addressWord (takenMemory wide p) post
    af2 (by rw [inst];exact takenCode.module) hcode.memoryIndex (taken_memory wide s op p hm)
    hcode.wordAddress (by rw [inst];exact takenCode.wordFunction) wt.1 (by rw [wt.2.1];exact hn.memoryWidth)
    wordInputBound wordSourceBound wordOutputBound takeRead takeLen hd
    (cTaken.mono (by rw [wordCost];cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> omega))
    (by simpa only [wordAfter,readWords,wordArguments,wordOut,op] using status)
  have wc : (StateDecodeWords.bodyCost wide+18)*cfg.regularOpCost+(5*op+rest)=(if wide then 46 else 38)*op+rest := by
    rw [wordCost]
    cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true,op] <;> omega
  have wfuel : fuel+5+StateDecodeWords.bodySteps wide+9=fuel+(if wide then 39 else 31) := by
    have eq : 5+StateDecodeWords.bodySteps wide+9=if wide then 39 else 31 := by cases wide <;> rfl
    omega
  rw [wc,wfuel] at word
  have guardedCode : Code wide (guarded s op p) frame.inst p := by
    have cr:=hcode.reserved wide s op frame.inst p
    apply cr.transport
    · simpa only [guarded] using paid_funcs (reserved s op p) op 6
    · simpa only [guarded] using paid_modules (reserved s op p) op 6
  have guardedMem : (guarded s op p).mems[p.memoryIndex]?=some p.memory := by
    unfold guarded
    rw [paid_memory,reserved_memory]
    exact hm
  have lengthAccepted : (WNear.Binary.StateDecodeScalar.width wide).toNat≤p.length.toNat := by cases wide <;> exact hn.lengthAccepted
  have takeBound : (scratch p+WNear.Binary.StateDecodeScalar.takeOffset wide).toNat+8≤p.memory.byteSize :=
    Nat.le_trans span.1 hn.spBound
  have cGuard := guarded_credits wide cfg s p ((if wide then 76 else 68)*op+rest)
    (hc.mono (by cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true,op] <;> omega))
  have take := wp_take_call cfg (fuel+(if wide then 39 else 31)) ((if wide then 46 else 38)*op+rest)
    (guarded s op p) limits base af callers
    (WNear.Binary.StateDecodeScalar.wordArguments wide++WNear.Binary.StateDecodeScalar.statusGuard wide++successTail wide)
    wide (scratch p) p.slice p.pointer p.length p.mi p.memoryIndex p.addressTake p.memory post
    af1 af2 af3 (by rw [inst];exact guardedCode.module) hcode.memoryIndex guardedMem
    hcode.takeAddress (by rw [inst];exact guardedCode.takeFunction) hn.wf
    (by have h:=hn.sliceBound;omega) takeBound hn.pointerRead lengthAccepted hd
    (cGuard.mono (by cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega))
    (by simpa only [takeAfter,taken,takeArguments,takeOut,width,op,List.append_assoc] using word)
  have tc : 30*cfg.regularOpCost+((if wide then 46 else 38)*op+rest)=(if wide then 76 else 68)*op+rest := by
    cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true,op] <;> omega
  have tf : fuel+(if wide then 39 else 31)+21=fuel+(if wide then 60 else 52) := by
    cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  rw [tc,tf] at take
  have reservedCode:=hcode.reserved wide s op frame.inst p
  have lengthFrameEq : lengthFrame inner p.memory p.slice=af := by
    simp only [lengthFrame,hn.lengthRead,inner,outer,af,acceptedFrame,guardedFrame,emptyBlockFrame]
  have inner1 : inner.locals[1]?=some (.i32 p.slice) := by
    simpa [inner,outer,emptyBlockFrame,reservedFrame,Array.set!,show 2<frame.locals.size by omega] using h1
  have innerInst : inner.inst=frame.inst:=rfl
  have cReserved:=reserved_credits wide cfg s p ((if wide then 82 else 74)*op+rest)
    (hc.mono (by cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true,op] <;> omega))
  have guard := wp_length_guard cfg (fuel+(if wide then 60 else 52)) ((if wide then 76 else 68)*op+rest)
    (reserved s op p) limits base.toArray inner callers
    (WNear.Binary.StateDecodeScalar.takeArguments wide++WNear.Binary.StateDecodeScalar.wordArguments wide++
      WNear.Binary.StateDecodeScalar.statusGuard wide++successTail wide)
    wide p.slice p.mi p.memoryIndex p.memory post inner1 (by rw [innerInst];exact reservedCode.module)
    hcode.memoryIndex (by rw [reserved_memory];exact hm) hn.sliceBound
    (by rw [hn.lengthRead];exact lengthAccepted)
    (cReserved.mono (by cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega))
    (by simpa only [guarded,lengthFrameEq,List.append_assoc] using take)
  have gc : 6*cfg.regularOpCost+((if wide then 76 else 68)*op+rest)=(if wide then 82 else 74)*op+rest := by
    cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true,op] <;> omega
  have gf : fuel+(if wide then 60 else 52)+7=fuel+(if wide then 67 else 59) := by
    cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  rw [gc,gf] at guard
  let inside := [.block .empty (WNear.Binary.StateDecodeScalar.lengthGuard wide++WNear.Binary.StateDecodeScalar.tooShort)]++
    WNear.Binary.StateDecodeScalar.takeArguments wide++WNear.Binary.StateDecodeScalar.wordArguments wide++
    WNear.Binary.StateDecodeScalar.statusGuard wide++successTail wide
  have innerWP : WP cfg (fuel+(if wide then 67 else 59)) (.next (atCode (reserved s op p) limits base.toArray inner callers inside))
      ((if wide then 82 else 74)*op+rest) post := by
    simpa only [inside,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using guard
  have blockInner := wp_block_empty cfg (fuel+(if wide then 67 else 59)) ((if wide then 82 else 74)*op+rest)
    (reserved s op p) limits base.toArray outer callers inside WNear.Binary.StateDecodeScalar.finish post cReserved
    (by simpa only [inner,List.size_toArray] using innerWP)
  have blockOuter := wp_block_empty cfg (fuel+(if wide then 67 else 59)+1) ((if wide then 82 else 74)*op+rest)
    (reserved s op p) limits base.toArray (reservedFrame frame p) callers
    ([.block .empty inside]++WNear.Binary.StateDecodeScalar.finish) (WNear.Binary.StateDecodeScalar.invalid wide++code)
    post cReserved (by simpa only [outer,List.size_toArray,List.singleton_append,List.cons_append,List.nil_append] using blockInner)
  have setup := wp_setup cfg (fuel+(if wide then 67 else 59)+1+1) ((if wide then 82 else 74)*op+rest)
    s limits base.toArray frame callers
    ([.block .empty ([.block .empty inside]++WNear.Binary.StateDecodeScalar.finish)]++WNear.Binary.StateDecodeScalar.invalid wide++code)
    p post hcode.module hcode.globalIndex hg hv
    (hc.mono (by cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true,op] <;> omega))
    (by simpa only [op,List.singleton_append,List.cons_append,List.nil_append,List.append_assoc] using blockOuter)
  have sf : fuel+(if wide then 67 else 59)+1+1+5=fuel+(if wide then 74 else 66) := by
    cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  have sc : 5*cfg.regularOpCost+((if wide then 82 else 74)*op+rest)=(if wide then 87 else 79)*cfg.regularOpCost+rest := by
    cases wide <;> simp only [Bool.false_eq_true,ite_false,ite_true,op] <;> omega
  rw [sf,sc] at setup
  simpa only [WNear.Binary.StateDecodeScalar.body,WNear.Binary.StateDecodeScalar.accepted,successTail,
    inside,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using setup
end WNear.Proofs.StateDecodeScalar
