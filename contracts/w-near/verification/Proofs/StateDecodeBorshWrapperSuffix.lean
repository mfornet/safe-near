import Proofs.StateDecodeBorshWrapperCopyCall
import Proofs.StateDecodeBorshWrapperPacked
import Proofs.StateDecodeBorshWrapperFinish
import Proofs.StateDecodeBorshWrapperNative
import Proofs.StateDecodeBorshWrapperFrame
import Proofs.StateDecodeBorshWrapperGas
import Proofs.StateDecodeBorshWrapperLocals

/-! Complete accepted162 suffix after cached425 output: both real36-byte
copies, status branch, packed store, caller record and shadow-stack restore. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode tagCached copied guarded packedSaved outputCopied accepted after
  decodedMemory firstMemory packedMemory secondMemory finalMemory packedValue tagValue tagFrame guardedFrame finalFrame
  readI32 readI64 writeI32 writeI64
private theorem paid_plus(s:Store NearState)(op a b:Nat):paid (paid s op a) op b=paid s op (a+b):=by
  induction b with
  |zero=>rfl
  |succ b ih=>change chargedStore (paid (paid s op a) op b) op=chargedStore (paid s op (a+b)) op;rw[ih]
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def suffixCode:Expr:=firstCopyCode++[.call 951]++prepareGuardCode++[.block .empty ([.block .empty acceptedCode]++errorCode)]++finishCode
private theorem finish_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p):
    finishStore (accepted cfg s p q) cfg.regularOpCost p.memoryIndex p.globalIndex (secondMemory p q) p.out162 (scratch p)=after cfg s p q:=by
  unfold finishStore after tagged
  rw[(scratch_numbers p hn).2.2.2]
private theorem packed_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    packedStore (guarded cfg s p q) cfg.regularOpCost p.memoryIndex (firstMemory p q) p.out162 (packedValue p q)=packedSaved cfg s p q:=by unfold packedStore packedSaved;rfl
private theorem copy_first_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    copyDropStore true (tagCached cfg s p q) cfg.regularOpCost p.memoryIndex (decodedMemory p q) p.out162 (scratch p)=paid (copied cfg s p q) cfg.regularOpCost 1:=by
  unfold copyDropStore copyDestination copySource copyArgumentCost copied copyArguments
  rfl
private theorem copy_second_eq(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    copyDropStore false (packedSaved cfg s p q) cfg.regularOpCost p.memoryIndex (packedMemory p q) p.out162 (scratch p)=paid (outputCopied cfg s p q) cfg.regularOpCost 1:=by
  unfold copyDropStore copyDestination copySource copyArgumentCost outputCopied outputArguments
  rfl

theorem wp_suffix(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global162)
    (h0:frame.locals[0]?=some (.i32 p.out162))(h1:frame.locals[1]?=some (.i32 p.slice))(hs:5≤frame.locals.size)
    (hdepth:callers.length+1<limits.maxCallDepth)(hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+1291) (.next (atCode (tagCached cfg s p q) limits base.toArray (tagFrame frame p q) callers
      (suffixCode++code))) (1371*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=guardedFrame frame p q
  let n:=emptyBlockFrame (emptyBlockFrame f base.toArray.size (finishCode++code)) base.toArray.size errorCode
  have ni:n.inst=frame.inst:=by simp only[n,f,emptyBlockFrame,guardedFrame_inst]
  have fl:=final_locals frame p q hs h0 h1
  have gl:=guarded_locals frame p q hs h0 h1
  have tl:=tag_locals frame p q hs h0 h1
  have sf:=secondMemory_spec p q hn hd
  have bound:=hn.outputBound
  have globals:(accepted cfg s p q).globals[p.globalIndex]?=some {p.global162 with value:=.i32 (scratch p)}:=by
    rw[accepted_globals cfg s p q hn hd hg];exact reserved_global s op p hg
  have finish:=wp_finish cfg fuel rest (accepted cfg s p q) limits base.toArray (finalFrame frame p q) callers code p.out162 (scratch p)
    p.mi p.memoryIndex p.globalIndex {p.global162 with value:=.i32 (scratch p)} (secondMemory p q) post fl.1 fl.2.1 fl.2.2.1
    (by rw[finalFrame_inst,(accepted_fields cfg s p q).2.1];exact hcode.child.prefixCode.child.module)
    hcode.child.prefixCode.child.memoryIndex (accepted_memory cfg s p q hn hd hm) hcode.child.prefixCode.child.globalIndex globals
    (by rw[sf.2.1];omega)
    (accepted_credits cfg s p q hn hd (7*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega)))
    (by rw[finish_eq cfg s p q hn];exact hnext)
  let ending:Expr:=[.i32_const 0,.local_set 1,.br 1]
  have accept:=wp_accept_exit cfg (fuel+7) (7*op+rest) (paid (outputCopied cfg s p q) op 1) limits base.toArray f callers
    (finishCode++code) errorCode [] post
    (paid_credits (outputCopied cfg s p q) op 1 _ ((outputCopied_credits cfg s p q hn hd (11*op+rest)
      (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by dsimp[op];omega)))
    (by rw[flagFrame_final_eq];simpa only[accepted,paid_plus,Nat.reduceAdd,op] using finish)
  have sp:=packedMemory_spec p q hn hd
  have sb:=second_copy_bounds p q hn hd
  have copy2:=wp_copy_call false cfg (fuel+10) (10*op+rest) (packedSaved cfg s p q) limits base n callers (ending++[]) p.out162 (scratch p)
    p.mi p.memoryIndex p.address951 (packedMemory p q) post gl.1 gl.2.2.1
    (by rw[ni];rw[(packedSaved_fields cfg s p q).2.1];exact hcode.child.prefixCode.child.module)
    hcode.child.prefixCode.child.memoryIndex (packedSaved_memory cfg s p q hn hd hm) hcode.index951
    (by rw[(packedSaved_fields cfg s p q).1,ni];exact hcode.function951)
    sp.1 (by rw[sp.2.1];exact hn.child.prefixNative.child.memoryWidth) sb.2 sb.1 hdepth
    ((packedSaved_credits cfg s p q hn hd (683*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by simp only[Bool.false_eq_true,ite_false];dsimp[op];omega))
    (by rw[copy_second_eq];simpa only[f,n,ending,List.append_nil,Nat.add_assoc,Nat.reduceAdd,
      show 3*cfg.regularOpCost+(7*op+rest)=10*op+rest by dsimp[op];omega] using accept)
  let afterPacked:=secondCopyCode++[.call 951,.drop]++ending
  have sm:=firstMemory_spec p q hn hd
  have a8:(p.out162+8).toNat+4≤(firstMemory p q).byteSize:=by
    have a:(p.out162+8).toNat=p.out162.toNat+8:=output_add p hn 8 (by omega)
    rw[sm.2.1,a];omega
  have packed:=wp_packed_store cfg (fuel+642) (683*op+rest) (guarded cfg s p q) limits base.toArray n callers afterPacked
    p.out162 (packedValue p q) p.mi p.memoryIndex (firstMemory p q) post gl.1 gl.2.2.2.1
    (by rw[ni];rw[(guarded_fields cfg s p q).2.1];exact hcode.child.prefixCode.child.module)
    hcode.child.prefixCode.child.memoryIndex (guarded_memory cfg s p q hn hd hm) a8
    ((guarded_credits cfg s p q hn hd (690*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by dsimp[op];omega))
    (by rw[packed_eq];simpa only[afterPacked,Bool.false_eq_true,ite_false,List.append_nil,Nat.add_assoc,Nat.reduceAdd,
      show 673*cfg.regularOpCost+(10*op+rest)=683*op+rest by dsimp[op];omega] using copy2)
  have copiedCredit: (copied cfg s p q).host.gas.Credits (697*op+rest):=
    copied_credits cfg s p q hn hd _ (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
  have guard:=wp_accepted_guard cfg (fuel+649) (690*op+rest) (paid (copied cfg s p q) op 3) limits base.toArray n callers
    (packedStoreCode++afterPacked) (tagValue p q) post gl.2.2.2.2.1 (by rw[tagValue_zero p q hn hd];decide)
    (paid_credits (copied cfg s p q) op 3 _ (copiedCredit.mono (by dsimp[op];omega)))
    (by simpa only[guarded,paid_plus,Nat.reduceAdd,op,Nat.add_assoc,
      show 7*cfg.regularOpCost+(683*op+rest)=690*op+rest by dsimp[op];omega] using packed)
  have acceptedBody:WP cfg (fuel+653) (.next (atCode (paid (copied cfg s p q) op 3) limits base.toArray n callers acceptedCode)) (694*op+rest) post:=by
    simpa only[acceptedCode,acceptedExitCode,afterPacked,ending,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 4*cfg.regularOpCost+(690*op+rest)=694*op+rest by dsimp[op];omega] using guard
  have inner:=wp_block_empty cfg (fuel+653) (694*op+rest) (paid (copied cfg s p q) op 3) limits base.toArray
    (emptyBlockFrame f base.toArray.size (finishCode++code)) callers acceptedCode errorCode post
    (paid_credits (copied cfg s p q) op 3 _ (copiedCredit.mono (by omega))) acceptedBody
  have outer:=wp_block_empty cfg (fuel+654) (694*op+rest) (paid (copied cfg s p q) op 3) limits base.toArray f callers
    ([.block .empty acceptedCode]++errorCode) (finishCode++code) post
    (paid_credits (copied cfg s p q) op 3 _ (copiedCredit.mono (by omega)))
    (by simpa only[n,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using inner)
  let tailCode:Expr:=[.block .empty ([.block .empty acceptedCode]++errorCode)]++finishCode++code
  have flag:=wp_flag cfg (fuel+655) (694*op+rest) (paid (copied cfg s p q) op 1) limits base.toArray (tagFrame frame p q) callers tailCode 1 post
    (paid_credits (copied cfg s p q) op 1 _ (copiedCredit.mono (by dsimp[op];omega)))
    (by rw[flagFrame_guarded_eq];simpa only[f,paid_plus,op,tailCode,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using outer)
  have shape:=decodedMemory_spec p q hn hd
  have fb:=first_copy_bounds p q hn hd
  have copy1:=wp_copy_call true cfg (fuel+657) (696*op+rest) (tagCached cfg s p q) limits base (tagFrame frame p q) callers
    (.i32_const 1::.local_set 1::tailCode) p.out162 (scratch p) p.mi p.memoryIndex p.address951 (decodedMemory p q) post tl.1 tl.2.2.1
    (by rw[tagFrame_inst,(tagCached_fields cfg s p q).2.1];exact hcode.child.prefixCode.child.module)
    hcode.child.prefixCode.child.memoryIndex (tagCached_memory cfg s p q hn hd hm) hcode.index951
    (by rw[(tagCached_fields cfg s p q).1,tagFrame_inst];exact hcode.function951) shape.1
    (by rw[shape.2.1];exact hn.child.prefixNative.child.memoryWidth) fb.2 fb.1 hdepth
    ((tagCached_credits cfg s p q hn hd (1371*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by simp only[ite_true];dsimp[op];omega))
    (by rw[copy_first_eq];simpa only[op,Nat.add_assoc,Nat.reduceAdd,
      show 2*cfg.regularOpCost+(694*op+rest)=696*op+rest by dsimp[op];omega] using flag)
  simpa only[suffixCode,prepareGuardCode,tailCode,ite_true,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 675*cfg.regularOpCost+(696*op+rest)=1371*cfg.regularOpCost+rest by dsimp[op];omega] using copy1
end WNear.Proofs.StateDecodeBorshWrapper
