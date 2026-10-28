import Proofs.DeallocateInsertStore
import Proofs.DeallocateInsertNext
import NearVM.MeteredLoopRules

/-! The four actual neighbor blocks select insertion without unlinking. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32
attribute [local irreducible] selected linked neighborAfter linkedMemory

def neighborFrame(frame:CallFrame)(p:Layout):=
  disabledNextFrame (Deallocate.previousFrame frame p.previous) (readI32 (zeroMemory p) p.header.toNat)

private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
/-- Actual previous-allocated and next-disabled control: four free block
entries, one natural inner end, a depth1exit, insertion, and allocator install. -/
theorem wp_neighbors(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(post:Post)
    (hcode:Code s frame.inst p)(hm:s.mems[p.memoryIndex]?=some (zeroMemory p))
    (ha:frame.locals[0]?=some (.i32 p.allocator))(hp:frame.locals[1]?=some (.i32 p.pointer))
    (hh:frame.locals[2]?=some (.i32 p.header))(ho:frame.locals[4]?=some (.i32 (oldHead p)))
    (hs:7≤frame.locals.size)(hn:Native p)(hc:s.host.gas.Credits (38*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (neighborAfter s cfg.regularOpCost p) limits base.toArray
      (neighborFrame frame p) callers code)) rest post):
    WP cfg (fuel+44) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.Deallocate.inspectNeighbors++WNear.Binary.Deallocate.installHead++code)))
      (38*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let label:Label:={arity:=0,height:=base.toArray.size,rest:=WNear.Binary.Deallocate.installHead++code,loop:=none}
  let first:=emptyBlockFrame frame base.toArray.size label.rest
  let second:=emptyBlockFrame first base.toArray.size WNear.Binary.Deallocate.insertHead
  let third:=emptyBlockFrame second base.toArray.size WNear.Binary.Deallocate.mergePrevious
  let word:=readI32 (zeroMemory p) p.header.toNat
  let f:=neighborFrame frame p
  let updated:=Deallocate.previousFrame frame p.previous
  have f0:f.locals[0]?=some (.i32 p.allocator):=by
    simpa only[f,neighborFrame,disabledNextFrame,maskedNextFrame,rawNextFrame,Deallocate.previousFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide:5≠0),Array.getElem?_setIfInBounds_ne (by decide:6≠0)] using ha
  have f1:f.locals[1]?=some (.i32 p.pointer):=by
    simpa only[f,neighborFrame,disabledNextFrame,maskedNextFrame,rawNextFrame,Deallocate.previousFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide:5≠1),Array.getElem?_setIfInBounds_ne (by decide:6≠1)] using hp
  have f2:f.locals[2]?=some (.i32 p.header):=by
    simpa only[f,neighborFrame,disabledNextFrame,maskedNextFrame,rawNextFrame,Deallocate.previousFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide:5≠2),Array.getElem?_setIfInBounds_ne (by decide:6≠2)] using hh
  have f4:f.locals[4]?=some (.i32 (oldHead p)):=by
    simpa only[f,neighborFrame,disabledNextFrame,maskedNextFrame,rawNextFrame,Deallocate.previousFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide:5≠4),Array.getElem?_setIfInBounds_ne (by decide:6≠4)] using ho
  have fi:f.inst=frame.inst:=rfl
  have a:(selected s op).host.gas.Credits (3*op+(3*op+rest)):=by
    simpa only[selected,show 6*op+rest=3*op+(3*op+rest) by omega] using paid_credits s op 32 (6*op+rest) (hc.mono (by dsimp[op];omega))
  have b:(linked s op p).host.gas.Credits (3*op+rest):=by
    simpa only[linked,storeI32] using paid_credits (selected s op) op 3 (3*op+rest) a
  have original:=writeI32_spec p.memory p.header.toNat (readI32 p.memory p.header.toNat&&&4294967294) hn.wf hn.headerBound
  have z:=writeI32_spec (markedMemory p) p.pointer.toNat 0 original.1 (by rw[show (markedMemory p).byteSize=p.memory.byteSize from original.2.1];exact hn.pointerBound)
  have zs:(zeroMemory p).byteSize=p.memory.byteSize:=z.2.1.trans original.2.1
  have link:=writeI32_spec (zeroMemory p) p.pointer.toNat (oldHead p) z.1 (by rw[zs];exact hn.pointerBound)
  have lsize:(linkedMemory p).byteSize=(zeroMemory p).byteSize:=by simpa only[linkedMemory] using link.2.1
  have linkmem:(linked s op p).mems[p.memoryIndex]?=some (linkedMemory p):=by
    unfold linked linkedMemory
    apply storeI32_memory
    rw[paid_mems,selected,paid_mems];exact hm
  have install:=wp_store_locals cfg fuel rest (linked s op p) limits base.toArray f callers code p.allocator p.header 0 2
    p.mi p.memoryIndex (linkedMemory p) post f0 f2
    (by simpa only[linked,selected,storeI32_modules,paid_modules,fi] using hcode.module) hcode.memoryIndex linkmem
    (by rw[lsize,zs];exact hn.allocatorBound) b
    (by simpa only[neighborAfter,op,f] using hnext)
  have endLabel:=wp_end_label cfg (fuel+3) (3*op+rest) (linked s op p) limits base.toArray f callers label post b
    (by simpa only[label,op,WNear.Binary.Deallocate.installHead,List.cons_append,List.nil_append] using install)
  have insert:=wp_store_locals cfg (fuel+4) (3*op+rest) (selected s op) limits base.toArray
    (emptyBlockFrame f base.toArray.size label.rest) callers [] p.pointer (oldHead p) 1 4 p.mi p.memoryIndex (zeroMemory p) post f1 f4
    (by simpa only[selected,paid_modules,emptyBlockFrame,fi] using hcode.module) hcode.memoryIndex
    (by rw[selected,paid_mems];exact hm) (by rw[zs];exact hn.pointerBound) a
    (by simpa only[linked,op,emptyBlockFrame,label] using endLabel)
  have nextAfter:WP cfg (fuel+7) (.next (atCode (paid (paid s op 15) op 17) limits base.toArray
      (disabledNextFrame (Deallocate.previousFrame first p.previous) word) callers WNear.Binary.Deallocate.insertHead)) (6*op+rest) post:=by
    simpa only[WNear.Binary.Deallocate.insertHead,selected,ValueReturnBorrow.paid_add,op,word,label,Nat.reduceAdd,show 3*cfg.regularOpCost+(3*cfg.regularOpCost+rest)=6*cfg.regularOpCost+rest by omega,f,neighborFrame,first,disabledNextFrame,maskedNextFrame,rawNextFrame,Deallocate.previousFrame,emptyBlockFrame,List.append_nil] using insert
  have selectedCode:(paid s op 15).modules[(Deallocate.previousFrame first p.previous).inst]?=some p.mi:=by
    simpa only[paid_modules,Deallocate.previousFrame,first,emptyBlockFrame] using hcode.module
  have next:=wp_next_disabled cfg (fuel+7) (6*op+rest) (paid s op 15) limits base.toArray
    (Deallocate.previousFrame first p.previous) callers WNear.Binary.Deallocate.insertHead WNear.Binary.Deallocate.mergePrevious
    ((WNear.Binary.Deallocate.nextGuard.drop 17)++WNear.Binary.Deallocate.linkNext) p.header p.mi p.memoryIndex (zeroMemory p) post
    (by simpa only[Deallocate.previousFrame,first,emptyBlockFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide:5≠2)] using hh)
    (by simp only[Deallocate.previousFrame,first,emptyBlockFrame,Array.size_set!];exact hs)
    selectedCode hcode.memoryIndex (by rw[paid_mems];exact hm) hn.nextWordBound hn.nextAddressNonzero hn.nextDisabled
    (paid_credits s op 15 _ (hc.mono (by dsimp[op];omega))) nextAfter
  have nextCode:(WNear.Binary.Deallocate.nextGuard.take 17)++((WNear.Binary.Deallocate.nextGuard.drop 17)++WNear.Binary.Deallocate.linkNext)=
      WNear.Binary.Deallocate.nextGuard++WNear.Binary.Deallocate.linkNext:=by rw[←List.append_assoc,List.take_append_drop]
  rw[nextCode] at next
  have endPrevious:=wp_end_label cfg (fuel+24) (23*op+rest) (paid s op 15) limits base.toArray
    (Deallocate.previousFrame third p.previous) callers
    {arity:=0,height:=base.toArray.size,rest:=WNear.Binary.Deallocate.nextGuard++WNear.Binary.Deallocate.linkNext,loop:=none} post
    (paid_credits s op 15 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[first,second,third,Deallocate.previousFrame,emptyBlockFrame,op,Nat.add_assoc,Nat.reduceAdd,
      show 17*cfg.regularOpCost+(6*op+rest)=23*op+rest by dsimp[op];omega] using next)
  have previous:=wp_previous_guard cfg (fuel+25) (23*op+rest) s limits base.toArray
    (emptyBlockFrame third base.toArray.size (WNear.Binary.Deallocate.nextGuard++WNear.Binary.Deallocate.linkNext)) callers []
    p.pointer p.previousAddress p.previous p.mi p.memoryIndex (zeroMemory p) post hp (by simp only[first,second,third,emptyBlockFrame];omega)
    hn.previousAddressEq hn.previousRead (by simpa only[first,second,third,emptyBlockFrame] using hcode.module) hcode.memoryIndex hm
    hn.previousAddressBound hn.previousNonzero hn.previousBound hn.previousAllocated (hc.mono (by dsimp[op];omega))
    (by simpa only[Deallocate.previousFrame,emptyBlockFrame,op] using endPrevious)
  unfold WNear.Binary.Deallocate.inspectNeighbors
  apply wp_block_empty cfg (fuel+43) _ s limits base.toArray frame callers _ (WNear.Binary.Deallocate.installHead++code) post hc
  apply wp_block_empty cfg (fuel+42) _ s limits base.toArray first callers _ WNear.Binary.Deallocate.insertHead post hc
  apply wp_block_empty cfg (fuel+41) _ s limits base.toArray second callers _ WNear.Binary.Deallocate.mergePrevious post hc
  apply wp_block_empty cfg (fuel+40) _ s limits base.toArray third callers _ (WNear.Binary.Deallocate.nextGuard++WNear.Binary.Deallocate.linkNext) post hc
  simpa only[List.append_nil,Nat.add_assoc,Nat.reduceAdd,show 15*cfg.regularOpCost+(23*op+rest)=38*cfg.regularOpCost+rest by dsimp[op];omega] using previous
end WNear.Proofs.DeallocateInsert
