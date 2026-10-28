import Proofs.StateDecodeScalarCode
import Proofs.StateDecodeScalarGuard
import Proofs.StateDecodeScalarDropCache
import Proofs.StateDecodeScalarUpdate

/-! Original local-array bounds justify every cached accepted scalar frame. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI64 readI32

theorem cacheFrame_eq (wide : Bool) (frame : CallFrame) (p : Layout) :
    cacheFrame wide frame (wordMemory wide p) (scratch p)=cachedFrame wide frame p := by
  cases wide <;> simp only [cacheFrame,cachedFrame,loaded64Frame,highValue,lowValue,ite_true,Bool.false_eq_true,ite_false]

theorem dropCacheFrame_eq (wide : Bool) (frame : CallFrame) (p : Layout) :
    dropCacheFrame wide frame (droppedMemory wide p) (scratch p)=dropCachedFrame wide frame p := rfl

theorem lengthFrame_eq (wide : Bool) (frame : CallFrame) (p : Layout) (hn : Native wide p) :
    lengthFrame (reservedFrame frame p) p.memory p.slice=guardedFrame frame p := by
  simp only [lengthFrame,guardedFrame,hn.lengthRead]

theorem guarded_locals (wide : Bool) (frame : CallFrame) (p : Layout)
    (hs : (if wide then 7 else 6)≤frame.locals.size)
    (h0 : frame.locals[0]?=some (.i32 p.out)) (h1 : frame.locals[1]?=some (.i32 p.slice)) :
    (guardedFrame frame p).locals[0]?=some (.i32 p.out) ∧
    (guardedFrame frame p).locals[1]?=some (.i32 p.slice) ∧
    (guardedFrame frame p).locals[2]?=some (.i32 (scratch p)) ∧
    (guardedFrame frame p).locals[3]?=some (.i32 p.length) ∧
    (guardedFrame frame p).locals.size=frame.locals.size := by
  have size:4≤frame.locals.size:=by cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hs <;> omega
  simp [guardedFrame,reservedFrame,Array.set!,h0,h1,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega]

theorem cached_locals (wide : Bool) (frame : CallFrame) (p : Layout)
    (hs : (if wide then 7 else 6)≤frame.locals.size)
    (h0 : frame.locals[0]?=some (.i32 p.out)) (h1 : frame.locals[1]?=some (.i32 p.slice)) :
    (cachedFrame wide (guardedFrame frame p) p).locals[0]?=some (.i32 p.out) ∧
    (cachedFrame wide (guardedFrame frame p) p).locals[1]?=some (.i32 p.slice) ∧
    (cachedFrame wide (guardedFrame frame p) p).locals[2]?=some (.i32 (scratch p)) ∧
    (cachedFrame wide (guardedFrame frame p) p).locals[3]?=some (.i32 p.length) ∧
    (cachedFrame wide (guardedFrame frame p) p).locals[4]?=some (.i64 (if wide then highValue p else lowValue wide p)) ∧
    (wide=true→(cachedFrame wide (guardedFrame frame p) p).locals[5]?=some (.i64 (lowValue wide p))) ∧
    (cachedFrame wide (guardedFrame frame p) p).locals.size=frame.locals.size := by
  have size:6≤frame.locals.size:=by cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hs <;> omega
  cases wide <;> simp [cachedFrame,guardedFrame,reservedFrame,Array.set!,h0,h1,
    show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,
    show 4<frame.locals.size by omega,show 5<frame.locals.size by omega]

theorem dropCached_locals (wide : Bool) (frame : CallFrame) (p : Layout)
    (hs : (if wide then 7 else 6)≤frame.locals.size)
    (h0 : frame.locals[0]?=some (.i32 p.out)) (h1 : frame.locals[1]?=some (.i32 p.slice)) :
    let f:=dropCachedFrame wide (cachedFrame wide (guardedFrame frame p) p) p
    f.locals[0]?=some (.i32 p.out) ∧ f.locals[1]?=some (.i32 p.slice) ∧
    f.locals[2]?=some (.i32 (scratch p)) ∧ f.locals[3]?=some (.i32 p.length) ∧
    f.locals[4]?=some (.i64 (if wide then highValue p else lowValue wide p)) ∧
    (wide=true→f.locals[5]?=some (.i64 (lowValue wide p))) ∧
    f.locals[if wide then 6 else 5]?=some (.i64 (dropValue wide p)) ∧ f.locals.size=frame.locals.size := by
  cases wide with
  | false=>
    have size:6≤frame.locals.size:=hs
    simp [dropCachedFrame,cachedFrame,guardedFrame,reservedFrame,Array.set!,h0,h1,
      show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega,show 5<frame.locals.size by omega]
  | true=>
    have size:7≤frame.locals.size:=hs
    simp [dropCachedFrame,cachedFrame,guardedFrame,reservedFrame,Array.set!,h0,h1,
      show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega,
      show 5<frame.locals.size by omega,show 6<frame.locals.size by omega]

@[simp] theorem guardedFrame_inst (wide : Bool) (frame : CallFrame) (p : Layout) :
    (guardedFrame frame p).inst=frame.inst := by cases wide <;> rfl
@[simp] theorem guardedFrame_arity (wide : Bool) (frame : CallFrame) (p : Layout) :
    (guardedFrame frame p).arity=frame.arity := by cases wide <;> rfl
@[simp] theorem guardedFrame_height (wide : Bool) (frame : CallFrame) (p : Layout) :
    (guardedFrame frame p).height=frame.height := by cases wide <;> rfl
@[simp] theorem guardedFrame_labels (wide : Bool) (frame : CallFrame) (p : Layout) :
    (guardedFrame frame p).labels=frame.labels := by cases wide <;> rfl
@[simp] theorem cachedFrame_inst (wide : Bool) (frame : CallFrame) (p : Layout) :
    (cachedFrame wide frame p).inst=frame.inst := by cases wide <;> rfl
@[simp] theorem cachedFrame_arity (wide : Bool) (frame : CallFrame) (p : Layout) :
    (cachedFrame wide frame p).arity=frame.arity := by cases wide <;> rfl
@[simp] theorem cachedFrame_height (wide : Bool) (frame : CallFrame) (p : Layout) :
    (cachedFrame wide frame p).height=frame.height := by cases wide <;> rfl
@[simp] theorem cachedFrame_labels (wide : Bool) (frame : CallFrame) (p : Layout) :
    (cachedFrame wide frame p).labels=frame.labels := by cases wide <;> rfl
@[simp] theorem dropCachedFrame_inst (wide : Bool) (frame : CallFrame) (p : Layout) :
    (dropCachedFrame wide frame p).inst=frame.inst := by cases wide <;> rfl
@[simp] theorem dropCachedFrame_arity (wide : Bool) (frame : CallFrame) (p : Layout) :
    (dropCachedFrame wide frame p).arity=frame.arity := by cases wide <;> rfl
@[simp] theorem dropCachedFrame_height (wide : Bool) (frame : CallFrame) (p : Layout) :
    (dropCachedFrame wide frame p).height=frame.height := by cases wide <;> rfl
@[simp] theorem dropCachedFrame_labels (wide : Bool) (frame : CallFrame) (p : Layout) :
    (dropCachedFrame wide frame p).labels=frame.labels := by cases wide <;> rfl

theorem zero_locals (frame : CallFrame) (out scratch : UInt32) (hs : 3≤frame.locals.size)
    (h0 : frame.locals[0]?=some (.i32 out)) (h2 : frame.locals[2]?=some (.i32 scratch)) :
    (zeroFrame frame).locals[0]?=some (.i32 out) ∧
    (zeroFrame frame).locals[1]?=some (.i32 0) ∧
    (zeroFrame frame).locals[2]?=some (.i32 scratch) ∧
    (zeroFrame frame).locals.size=frame.locals.size := by
  simp [zeroFrame,Array.set!,h0,h2,show 1<frame.locals.size by omega]

end WNear.Proofs.StateDecodeScalar
