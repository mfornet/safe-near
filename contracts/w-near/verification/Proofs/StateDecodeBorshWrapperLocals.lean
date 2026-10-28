import Proofs.StateDecodeBorshWrapperState
import Proofs.StateDecodeBorshWrapperControl

/-! The five-local162 frame supports every deployed cache and status write. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 decodedMemory packedValue tagValue

theorem loadedTagFrame_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    loadedTagFrame (reservedFrame frame p) (decodedMemory p q) (scratch p)=tagFrame frame p q:=by
  simp only[loadedTagFrame,tagSnapshotFrame,StateDecodeScalar.loaded64Frame,tagFrame,packedFrame,packedValue,tagValue]

theorem flagFrame_guarded_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    flagFrame (tagFrame frame p q) 1=guardedFrame frame p q:=rfl

theorem flagFrame_final_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    flagFrame (guardedFrame frame p q) 0=finalFrame frame p q:=rfl

theorem loaded64Frame_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    StateDecodeScalar.loaded64Frame (reservedFrame frame p) 3
      (readI64 (decodedMemory p q) ((scratch p).toNat+52))=packedFrame frame p q:=by
  simp only[StateDecodeScalar.loaded64Frame,packedFrame,packedValue]

theorem reserved_locals(frame:CallFrame)(p:Layout)
    (hs:5≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out162))(h1:frame.locals[1]?=some (.i32 p.slice)):
    (reservedFrame frame p).locals[0]?=some (.i32 p.out162) ∧
    (reservedFrame frame p).locals[1]?=some (.i32 p.slice) ∧
    (reservedFrame frame p).locals[2]?=some (.i32 (scratch p)) ∧
    (reservedFrame frame p).locals.size=frame.locals.size:=by
  simp [reservedFrame,Array.set!,h0,h1,
    show 2<frame.locals.size by omega]

@[simp] theorem reservedFrame_inst(frame:CallFrame)(p:Layout):
    (reservedFrame frame p).inst=frame.inst:=by simp only[reservedFrame]

@[simp] theorem reservedFrame_arity(frame:CallFrame)(p:Layout):
    (reservedFrame frame p).arity=frame.arity:=by simp only[reservedFrame]

@[simp] theorem reservedFrame_height(frame:CallFrame)(p:Layout):
    (reservedFrame frame p).height=frame.height:=by simp only[reservedFrame]

@[simp] theorem reservedFrame_labels(frame:CallFrame)(p:Layout):
    (reservedFrame frame p).labels=frame.labels:=by simp only[reservedFrame]

theorem packed_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:5≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out162))(h1:frame.locals[1]?=some (.i32 p.slice)):
    (packedFrame frame p q).locals[0]?=some (.i32 p.out162) ∧
    (packedFrame frame p q).locals[1]?=some (.i32 p.slice) ∧
    (packedFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (packedFrame frame p q).locals[3]?=some (.i64 (packedValue p q)) ∧
    (packedFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,packedFrame,Array.set!,h0,h1,
    show 2<frame.locals.size by omega,show 3<frame.locals.size by omega]

@[simp] theorem packedFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedFrame frame p q).inst=frame.inst:=by simp only[packedFrame,reservedFrame_inst]

@[simp] theorem packedFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedFrame frame p q).arity=frame.arity:=by simp only[packedFrame,reservedFrame_arity]

@[simp] theorem packedFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedFrame frame p q).height=frame.height:=by simp only[packedFrame,reservedFrame_height]

@[simp] theorem packedFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedFrame frame p q).labels=frame.labels:=by simp only[packedFrame,reservedFrame_labels]

theorem tag_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:5≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out162))(h1:frame.locals[1]?=some (.i32 p.slice)):
    (tagFrame frame p q).locals[0]?=some (.i32 p.out162) ∧
    (tagFrame frame p q).locals[1]?=some (.i32 p.slice) ∧
    (tagFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (tagFrame frame p q).locals[3]?=some (.i64 (packedValue p q)) ∧
    (tagFrame frame p q).locals[4]?=some (.i32 (tagValue p q)) ∧
    (tagFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,packedFrame,tagFrame,Array.set!,h0,h1,
    show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

@[simp] theorem tagFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagFrame frame p q).inst=frame.inst:=by simp only[tagFrame,packedFrame_inst]

@[simp] theorem tagFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagFrame frame p q).arity=frame.arity:=by simp only[tagFrame,packedFrame_arity]

@[simp] theorem tagFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagFrame frame p q).height=frame.height:=by simp only[tagFrame,packedFrame_height]

@[simp] theorem tagFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (tagFrame frame p q).labels=frame.labels:=by simp only[tagFrame,packedFrame_labels]

theorem guarded_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:5≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out162))(_h1:frame.locals[1]?=some (.i32 p.slice)):
    (guardedFrame frame p q).locals[0]?=some (.i32 p.out162) ∧
    (guardedFrame frame p q).locals[1]?=some (.i32 1) ∧
    (guardedFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (guardedFrame frame p q).locals[3]?=some (.i64 (packedValue p q)) ∧
    (guardedFrame frame p q).locals[4]?=some (.i32 (tagValue p q)) ∧
    (guardedFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,packedFrame,tagFrame,guardedFrame,Array.set!,h0,
    show 1<frame.locals.size by omega,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

@[simp] theorem guardedFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (guardedFrame frame p q).inst=frame.inst:=by simp only[guardedFrame,tagFrame_inst]

@[simp] theorem guardedFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (guardedFrame frame p q).arity=frame.arity:=by simp only[guardedFrame,tagFrame_arity]

@[simp] theorem guardedFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (guardedFrame frame p q).height=frame.height:=by simp only[guardedFrame,tagFrame_height]

@[simp] theorem guardedFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (guardedFrame frame p q).labels=frame.labels:=by simp only[guardedFrame,tagFrame_labels]

theorem final_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:5≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out162))(_h1:frame.locals[1]?=some (.i32 p.slice)):
    (finalFrame frame p q).locals[0]?=some (.i32 p.out162) ∧
    (finalFrame frame p q).locals[1]?=some (.i32 0) ∧
    (finalFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (finalFrame frame p q).locals[3]?=some (.i64 (packedValue p q)) ∧
    (finalFrame frame p q).locals[4]?=some (.i32 (tagValue p q)) ∧
    (finalFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,packedFrame,tagFrame,guardedFrame,finalFrame,Array.set!,h0,
    show 1<frame.locals.size by omega,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

@[simp] theorem finalFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).inst=frame.inst:=by simp only[finalFrame,guardedFrame_inst]

@[simp] theorem finalFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).arity=frame.arity:=by simp only[finalFrame,guardedFrame_arity]

@[simp] theorem finalFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).height=frame.height:=by simp only[finalFrame,guardedFrame_height]

@[simp] theorem finalFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).labels=frame.labels:=by simp only[finalFrame,guardedFrame_labels]
end WNear.Proofs.StateDecodeBorshWrapper
