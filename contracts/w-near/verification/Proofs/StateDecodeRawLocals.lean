import Proofs.StateDecodeRawPhases
import Proofs.StateDecodeRawMemory

/-! Original local-array bounds justify every actual767 selected local update. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic

theorem cachedPointer_eq (p : Layout) (hn : Native p) :
    cachedPointer p=readI32 (memory769 p) ((scratch p).toNat+16) := by
  have a:=record_numbers p hn
  have b:=stack_numbers p hn
  have lo:=hn.spLower
  unfold cachedPointer
  rw[a.2.1,b.1]
  congr 1;omega

theorem checkedRaw_locals (frame : CallFrame) (p : Layout) (hs : 6≤frame.locals.size)
    (h0 : frame.locals[0]?=some (.i32 p.outRaw)) (h2 : frame.locals[2]?=some (.i32 p.flag)) :
    let f:=checkedRawFrame frame p
    f.locals[0]?=some (.i32 p.outRaw) ∧ f.locals[1]?=some (.i32 1) ∧
    f.locals[2]?=some (.i32 p.flag) ∧ f.locals[3]?=some (.i32 (scratch p)) ∧
    f.locals[4]?=some (.i32 p.size) ∧f.locals.size=frame.locals.size := by
  simp[checkedRawFrame,alignedRawFrame,reservedRawFrame,AllocateVector.loadedFrame,Array.set!,h0,h2,
    show 1<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

theorem cachedRaw_locals (frame : CallFrame) (p : Layout) (hn : Native p) (hs : 6≤frame.locals.size)
    (h0 : frame.locals[0]?=some (.i32 p.outRaw)) (_h2 : frame.locals[2]?=some (.i32 p.flag)) :
    let f:=cachedRawFrame frame p
    f.locals[0]?=some (.i32 p.outRaw) ∧ f.locals[1]?=some (.i32 1) ∧
    f.locals[2]?=some (.i32 (cachedPointer p)) ∧f.locals[3]?=some (.i32 (scratch p)) ∧
    f.locals[4]?=some (.i32 p.size) ∧f.locals[5]?=some (.i32 (cachedLength p)) ∧f.locals.size=frame.locals.size := by
  rw[cachedPointer_eq p hn]
  simp[cachedRawFrame,cacheFrame,cachedLength,checkedRawFrame,alignedRawFrame,reservedRawFrame,AllocateVector.loadedFrame,Array.set!,h0,
    show 1<frame.locals.size by omega,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,
    show 4<frame.locals.size by omega,show 5<frame.locals.size by omega]

@[simp] theorem checkedRawFrame_inst (frame : CallFrame) (p : Layout) : (checkedRawFrame frame p).inst=frame.inst:=rfl
@[simp] theorem checkedRawFrame_arity (frame : CallFrame) (p : Layout) : (checkedRawFrame frame p).arity=frame.arity:=rfl
@[simp] theorem checkedRawFrame_height (frame : CallFrame) (p : Layout) : (checkedRawFrame frame p).height=frame.height:=rfl
@[simp] theorem checkedRawFrame_labels (frame : CallFrame) (p : Layout) : (checkedRawFrame frame p).labels=frame.labels:=rfl
@[simp] theorem cachedRawFrame_inst (frame : CallFrame) (p : Layout) : (cachedRawFrame frame p).inst=frame.inst:=rfl
@[simp] theorem cachedRawFrame_arity (frame : CallFrame) (p : Layout) : (cachedRawFrame frame p).arity=frame.arity:=rfl
@[simp] theorem cachedRawFrame_height (frame : CallFrame) (p : Layout) : (cachedRawFrame frame p).height=frame.height:=rfl
@[simp] theorem cachedRawFrame_labels (frame : CallFrame) (p : Layout) : (cachedRawFrame frame p).labels=frame.labels:=rfl
end WNear.Proofs.StateDecodeRaw
