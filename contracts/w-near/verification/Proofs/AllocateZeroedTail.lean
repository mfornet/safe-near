import Proofs.AllocateZeroedState
import NearVM.MeteredNumericRules
import NearVM.MeteredLoopRules

/-! The actual f153 nonzero-result guard, real symbolic memset, and normal block exit. -/
namespace WNear.Proofs.AllocateZeroed
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode ZeroFill.callAfter
set_option maxRecDepth 16384

def tailFilled (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32) :=
  ZeroFill.callAfter (paid (paid s op 3) op 3) op index memory ptr 0 len
def tailAfter (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32) :=
  paid (tailFilled s op index memory ptr len) op 2
def tailFrame (frame : CallFrame) (ptr : UInt32) := {frame with locals:=frame.locals.set! 0 (.i32 ptr)}

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with | zero=>rfl | succ n ih=>exact ih

 theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr len : UInt32) (mi : ModuleInst) (address index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 len)) (hsize : 0<frame.locals.size)
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.funcAddrs[952]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.ZeroFill.signature frame.inst WNear.Binary.ZeroFill.function))
    (hindex : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hn : ptr≠0) (hw : memory.wf) (hb : ptr.toNat+len.toNat≤memory.byteSize) (hwidth : ptr.toNat+len.toNat≤2^32)
    (hd : callers.length+1<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((ZeroFill.bodyCost len+19)*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (tailAfter s cfg.regularOpCost index memory ptr len) limits
      (base++[Value.i32 ptr]).toArray (tailFrame frame ptr) callers code)) rest post) :
    WP cfg (fuel+ZeroFill.bodySteps len+11) (.next (atCode s limits (base++[Value.i32 ptr]).toArray
      (emptyBlockFrame frame base.length (.local_get 0::code)) callers WNear.Binary.AllocateZeroed.fill))
      ((ZeroFill.bodyCost len+19)*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let f := tailFrame frame ptr
  let bf := emptyBlockFrame f base.length (.local_get 0::code)
  let full := tailFilled s op index memory ptr len
  have f0 : f.locals[0]?=some (.i32 ptr) := by simp [f,tailFrame,hsize]
  have f1 : bf.locals[1]?=some (.i32 len) := by simpa [bf,f,tailFrame,emptyBlockFrame] using h1
  have fillCredit : (paid (paid s op 3) op 3).host.gas.Credits ((ZeroFill.bodyCost len+11)*op+(2*op+rest)) := by
    apply paid_credits
    apply paid_credits
    exact hc.mono (by first | omega | (simp only [op, Nat.add_mul]; omega))
  have finalCredit : full.host.gas.Credits (2*op+rest) :=
    ZeroFill.callAfter_credits (paid (paid s op 3) op 3) op index _ memory ptr 0 len fillCredit
  have lastCredit := paid_credits full op 1 (op+rest) (finalCredit.mono (by omega))
  have arr : (base++[Value.i32 ptr]).toArray=base.toArray.push (.i32 ptr) := by apply Array.toList_inj.mp;simp
  have get := wp_local_get cfg fuel rest (paid full op 1) limits base.toArray f callers code 0 (.i32 ptr) post f0 lastCredit
    (by simpa only [tailAfter,full,op,paid,f,arr] using hnext)
  let label : Label := ⟨0,base.length,.local_get 0::code,none⟩
  have ending := wp_end_label cfg (fuel+1) (op+rest) (paid full op 1) limits base.toArray f callers label post lastCredit (by simpa only [label,op] using get)
  have ending' : WP cfg (fuel+2) (.next (atCode (paid full op 1) limits base.toArray bf callers [])) (op+rest) post := by
    simpa only [bf,label,emptyBlockFrame,Nat.add_assoc,Nat.reduceAdd] using ending
  have drop := wp_drop cfg (fuel+2) (op+rest) full limits base.toArray bf callers [] (.i32 ptr) post
    (finalCredit.mono (by omega)) ending'
  have callNext : WP cfg (fuel+3) (.next (atCode full limits (base++[Value.i32 ptr]).toArray bf callers [.drop])) (2*op+rest) post := by
    simpa only [arr,show cfg.regularOpCost+(op+rest)=2*op+rest by omega] using drop
  have hm6 : (paid (paid s op 3) op 3).modules[bf.inst]?=some mi := by rw [modules_paid,modules_paid];exact hm
  have hf6 : (paid (paid s op 3) op 3).funcs[address]?=some (.wasm WNear.Binary.ZeroFill.signature bf.inst WNear.Binary.ZeroFill.function) := by
    rw [funcs_paid,funcs_paid];exact hf
  have hmemb : (paid (paid s op 3) op 3).mems[index]?=some memory := by rw [mems_paid,mems_paid];exact hmem
  have call := ZeroFill.wp_call cfg (fuel+3) (2*op+rest) (paid (paid s op 3) op 3) limits base bf callers [.drop]
    ptr 0 len mi address index memory post hm6 hi hf6 hindex hmemb hw hb hwidth hd fillCredit callNext
  have c3 : (paid s op 3).host.gas.Credits ((ZeroFill.bodyCost len+16)*op+rest) :=
    paid_credits s op 3 _ (hc.mono (by first | omega | (simp only [op, Nat.add_mul]; omega)))
  have c4 := paid_credits (paid s op 3) op 1 ((ZeroFill.bodyCost len+15)*op+rest) (c3.mono (by first | omega | (simp only [op,Nat.add_mul];omega)))
  have c5 := paid_credits (paid s op 3) op 2 ((ZeroFill.bodyCost len+14)*op+rest) (c3.mono (by first | omega | (simp only [op,Nat.add_mul];omega)))
  have argsNext : WP cfg ((fuel+3)+ZeroFill.bodySteps len+2) (.next (atCode (paid (paid s op 3) op 3) limits
      (base++[Value.i32 ptr,.i32 0,.i32 len]).toArray bf callers [.call 952,.drop]))
      ((ZeroFill.bodyCost len+13)*op+rest) post := by
    simpa only [tailFilled,full,show (ZeroFill.bodyCost len+11)*cfg.regularOpCost+(2*op+rest)=(ZeroFill.bodyCost len+13)*op+rest by first | omega | (simp only [op, Nat.add_mul]; omega)] using call
  have arr3 : (base++[Value.i32 ptr,.i32 0,.i32 len]).toArray=((base.toArray.push (.i32 ptr)).push (.i32 0)).push (.i32 len) := by apply Array.toList_inj.mp;simp
  have getLen := wp_local_get cfg ((fuel+3)+ZeroFill.bodySteps len+2) ((ZeroFill.bodyCost len+13)*op+rest) (paid (paid s op 3) op 2) limits
    ((base.toArray.push (.i32 ptr)).push (.i32 0)) bf callers [.call 952,.drop] 1 (.i32 len) post f1
    (c5.mono (by first | omega | (simp only [op, Nat.add_mul]; omega))) (by simpa only [paid,op,arr3] using argsNext)
  have zero := wp_i32_const cfg (((fuel+3)+ZeroFill.bodySteps len+2)+1) _ (paid (paid s op 3) op 1) limits
    (base.toArray.push (.i32 ptr)) bf callers [.local_get 1,.call 952,.drop] 0 post (c4.mono (by first | omega | (simp only [op, Nat.add_mul]; omega))) getLen
  have getPtr := wp_local_get cfg ((((fuel+3)+ZeroFill.bodySteps len+2)+1)+1) _ (paid s op 3) limits base.toArray bf callers
    [.i32_const 0,.local_get 1,.call 952,.drop] 0 (.i32 ptr) post (by simpa [bf,emptyBlockFrame] using f0)
    (c3.mono (by first | omega | (simp only [op, Nat.add_mul]; omega))) zero
  have beforeArgs : WP cfg (fuel+ZeroFill.bodySteps len+8) (.next (atCode (paid s op 3) limits base.toArray bf callers
      [.local_get 0,.i32_const 0,.local_get 1,.call 952,.drop])) ((ZeroFill.bodyCost len+16)*op+rest) post := by
    have fe : ((((fuel+3)+ZeroFill.bodySteps len+2)+1)+1)+1=fuel+ZeroFill.bodySteps len+8 := by omega
    have ce : cfg.regularOpCost+(cfg.regularOpCost+(cfg.regularOpCost+((ZeroFill.bodyCost len+13)*op+rest)))=(ZeroFill.bodyCost len+16)*op+rest := by simp only [op,Nat.add_mul];omega
    simpa only [fe,ce] using getPtr

  have br := wp_br_if_zero cfg (fuel+ZeroFill.bodySteps len+8) ((ZeroFill.bodyCost len+16)*op+rest) (paid s op 2) limits
    base.toArray bf callers [.local_get 0,.i32_const 0,.local_get 1,.call 952,.drop] 0 post
    (paid_credits s op 2 _ (hc.mono (by first | omega | (simp only [op, Nat.add_mul]; omega)))) beforeArgs
  have eqz := wp_i32_eqz cfg (fuel+ZeroFill.bodySteps len+9) (op+((ZeroFill.bodyCost len+16)*op+rest)) (paid s op 1) limits base.toArray bf callers
    [.br_if 0,.local_get 0,.i32_const 0,.local_get 1,.call 952,.drop] ptr post
    (paid_credits s op 1 _ (hc.mono (by first | omega | (simp only [op, Nat.add_mul]; omega))))
    (by simpa [op,paid,Nat.add_assoc,Numeric.bool,show (ptr==0)=false from beq_eq_false_iff_ne.mpr hn] using br)
  have first := wp_local_tee cfg (fuel+ZeroFill.bodySteps len+10) (op+(op+((ZeroFill.bodyCost len+16)*op+rest))) s limits base.toArray
    (emptyBlockFrame frame base.length (.local_get 0::code)) callers
    [.i32_eqz,.br_if 0,.local_get 0,.i32_const 0,.local_get 1,.call 952,.drop] 0 (.i32 ptr) post
    (hc.mono (by first | omega | (simp only [op, Nat.add_mul]; omega))) (by simpa only [bf,f,tailFrame,emptyBlockFrame,op,paid,Nat.add_assoc,Nat.reduceAdd] using eqz)
  have fe : fuel+ZeroFill.bodySteps len+10+1=fuel+ZeroFill.bodySteps len+11 := by omega
  have ce : cfg.regularOpCost+(op+(op+((ZeroFill.bodyCost len+16)*op+rest)))=(ZeroFill.bodyCost len+19)*cfg.regularOpCost+rest := by simp only [op,Nat.add_mul];omega
  simpa only [WNear.Binary.AllocateZeroed.fill,arr,fe,ce] using first


end WNear.Proofs.AllocateZeroed
