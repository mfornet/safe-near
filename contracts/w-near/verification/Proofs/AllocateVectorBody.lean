import Proofs.AllocateVectorPrefix
import Proofs.AllocateVectorGuard
import Proofs.AllocateVectorAllocation
import Proofs.AllocateVectorSetupReadback

/-! Entire deployed686 accepted body, including685/684 and690's full growth allocation. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
attribute [local irreducible] WP atCode laidOut guarded after actualRecord derivedGrown laidOutMemory resultMemory

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p) (haRoot : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.out686)) (h1 : frame.locals[1]?=some (.i32 p.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (hs : 6≤frame.locals.size)
    (ha : frame.arity=0) (hh : frame.height=base.length)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.outerGlobal)
    (hv : p.outerGlobal.value=.i32 p.outerSP) (hd : callers.length+10<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame (caller::callers)
      (WNear.Binary.AllocateVector.body++code))) (bodyCost p*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let q := layout690 p
  let rf := reservedFrame frame p
  let outerExit : Expr := [.local_get 4,.local_get 1,.call 842,.unreachable]++code
  let ofr := emptyBlockFrame rf base.toArray.size outerExit
  let bf := emptyBlockFrame ofr base.toArray.size [.call 844,.unreachable]
  let af := loadedFrame bf 1 1
  let gf := guardedFrame bf p
  let remaining := (AllocateRecordCopy.bodyCost q+40)*op+fee cfg p+rest
  have gf0 : gf.locals[0]?=some (.i32 p.out686) := by simp [gf,guardedFrame,bf,ofr,emptyBlockFrame,rf,reservedFrame,h0]
  have gf1 : gf.locals[1]?=some (.i32 1) := by simp [gf,guardedFrame,bf,ofr,emptyBlockFrame,rf,reservedFrame,show 1<frame.locals.size by omega]
  have gf2 : gf.locals[2]?=some (.i32 1) := by simp [gf,guardedFrame,bf,ofr,emptyBlockFrame,rf,reservedFrame,h2]
  have gf3 : gf.locals[3]?=some (.i32 (reservedSP p)) := by simp [gf,guardedFrame,bf,ofr,emptyBlockFrame,rf,reservedFrame,show 3<frame.locals.size by omega]
  have gf4 : gf.locals[4]?=some (.i32 p.size) := by simp [gf,guardedFrame,bf,ofr,emptyBlockFrame,rf,reservedFrame,show 4<frame.locals.size by omega]
  have gfs : 6≤gf.locals.size := by simpa only [gf,guardedFrame,bf,ofr,emptyBlockFrame,rf,reservedFrame,Array.size_set!] using hs
  have gcd : Code s gf.inst p := by simpa only [gf,guardedFrame,bf,ofr,emptyBlockFrame,rf,reservedFrame] using hcode
  have al := wp_allocation cfg fuel rest s limits base gf caller callers p post hn gcd haRoot gf0 gf1 gf2 gf3 gf4 gfs ha hh hm hg hd hc hnext
  have orig := hcode.allocation.allocation.retry.originalCode
  have modules : (laidOut s op p).modules=s.modules := by
    simpa only [allocateArguments,selected,guarded,paid,chargedStore] using (allocateArguments_fields s op p).2.1
  have lm : (laidOut s op p).modules[bf.inst]?=some p.mi := by
    rw [modules];simpa only [bf,ofr,emptyBlockFrame,rf,reservedFrame,AllocatePositive.searchLayout] using orig.search.module
  have me := laidOut_memory s op p hm
  have bf3 : bf.locals[3]?=some (.i32 (reservedSP p)) := by simp [bf,ofr,emptyBlockFrame,rf,reservedFrame,show 3<frame.locals.size by omega]
  have af3 : af.locals[3]?=some (.i32 (reservedSP p)) := by simp [af,loadedFrame,bf3]
  have reads := setup_words p hn
  have bounds := setup_load_bounds p hn
  have cl : (laidOut s op p).host.gas.Credits (11*op+remaining) :=
    (laidOut_gas s op p _ (hc.mono (by simp only [bodyCost,remaining,q,Nat.add_mul,op];omega))).2.2
  have aln : WP cfg (fuel+AllocateRecordCopy.bodySteps q+33) (.next (atCode
      (paid (paid (laidOut s op p) op 5) op 6) limits base.toArray (loadedFrame af 4 p.size) (caller::callers)
      WNear.Binary.AllocateVector.accepted)) remaining post := by
    simpa only [guarded,paid,gf,guardedFrame,af,loadedFrame,remaining,q,op] using al
  have m5 : (paid (laidOut s op p) op 5).modules[af.inst]?=some p.mi := by
    simpa only [paid,chargedStore,af,loadedFrame] using lm
  have me5 : (paid (laidOut s op p) op 5).mems[p.memoryIndex]?=some (laidOutMemory p) := by
    simpa only [paid,chargedStore] using me
  have sizeG := wp_size_guard cfg (fuel+AllocateRecordCopy.bodySteps q+33) remaining (paid (laidOut s op p) op 5) limits base.toArray af (caller::callers)
    WNear.Binary.AllocateVector.accepted (reservedSP p) p.size p.mi p.memoryIndex (laidOutMemory p) post af3 m5 orig.search.memoryIndex me5
    (by omega) reads.1 hn.sizeBound (paid_credits (laidOut s op p) op 5 _ (cl.mono (by omega))) aln
  have an : WP cfg ((fuel+AllocateRecordCopy.bodySteps q+33)+6) (.next (atCode (paid (laidOut s op p) op 5) limits base.toArray af (caller::callers)
      ([.local_get 3,.load .i32 none {align:=2,offset:=24},.local_tee 4,.i32_const 4294967295,.i32_relop .le_s,.br_if 0]++WNear.Binary.AllocateVector.accepted)))
      (6*op+remaining) post := sizeG
  have alignG := wp_alignment_guard cfg ((fuel+AllocateRecordCopy.bodySteps q+33)+6) (6*op+remaining) (laidOut s op p) limits base.toArray bf (caller::callers)
    ([.local_get 3,.load .i32 none {align:=2,offset:=24},.local_tee 4,.i32_const 4294967295,.i32_relop .le_s,.br_if 0]++WNear.Binary.AllocateVector.accepted)
    (reservedSP p) p.mi p.memoryIndex (laidOutMemory p) post bf3 lm orig.search.memoryIndex me bounds reads.2 (cl.mono (by omega)) an
  have ce : 5*cfg.regularOpCost+(6*op+remaining)=(AllocateRecordCopy.bodyCost q+51)*op+fee cfg p+rest := by simp only [remaining,Nat.add_mul,op];omega
  rw [ce] at alignG
  let tailCost := (AllocateRecordCopy.bodyCost q+51)*op+fee cfg p+rest
  have ct : (laidOut s op p).host.gas.Credits tailCost :=
    (laidOut_gas s op p _ (hc.mono (by simp only [tailCost,bodyCost,q,Nat.add_mul,op];omega))).2.2
  have block1 := wp_block_empty cfg (((fuel+AllocateRecordCopy.bodySteps q+33)+6)+5) tailCost (laidOut s op p) limits base.toArray ofr (caller::callers)
    WNear.Binary.AllocateVector.checked [.call 844,.unreachable] post ct
    (by simpa only [bf,WNear.Binary.AllocateVector.checked,WNear.Binary.AllocateVector.guard,List.append_assoc,List.cons_append,List.nil_append] using alignG)
  have block2 := wp_block_empty cfg ((((fuel+AllocateRecordCopy.bodySteps q+33)+6)+5)+1) tailCost (laidOut s op p) limits base.toArray rf (caller::callers)
    [.block .empty WNear.Binary.AllocateVector.checked,.call 844,.unreachable] outerExit post ct block1
  have pref := wp_prefix cfg (((((fuel+AllocateRecordCopy.bodySteps q+33)+6)+5)+1)+1) tailCost s limits base frame (caller::callers)
    (.block .empty [.block .empty WNear.Binary.AllocateVector.checked,.call 844,.unreachable]::outerExit) p post hn hcode h1 hs hm hg hv
    (by simp only [List.length_cons];omega) (hc.mono (by simp only [tailCost,bodyCost,q,Nat.add_mul,op];omega)) block2
  have pe : 87*cfg.regularOpCost+tailCost=bodyCost p*cfg.regularOpCost+fee cfg p+rest := by simp only [tailCost,bodyCost,q,Nat.add_mul,op];omega
  rw [pe] at pref
  have fe : fuel+AllocateRecordCopy.bodySteps q+33+6+5+1+1+70=fuel+bodySteps p := by simp only [bodySteps,q];omega
  rw [fe] at pref
  simpa only [WNear.Binary.AllocateVector.body,outerExit,List.append_assoc,List.cons_append,List.nil_append] using pref
end WNear.Proofs.AllocateVector
