import Proofs.StateDecodeBorshReadPhases

/-! The actual161 five-local frame, including the original length until its
status overwrite. All cache writes preserve caller-frame metadata. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 wrappedMemory packedValue tagValue

theorem reserved_locals(frame:CallFrame)(p:Layout)
    (hs:5≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out161))
    (h1:frame.locals[1]?=some (.i32 p.pointer))(h2:frame.locals[2]?=some (.i32 p.length)):
    (reservedFrame frame p).locals[0]?=some (.i32 p.out161) ∧
    (reservedFrame frame p).locals[1]?=some (.i32 p.pointer) ∧
    (reservedFrame frame p).locals[2]?=some (.i32 p.length) ∧
    (reservedFrame frame p).locals[3]?=some (.i32 (scratch p)) ∧
    (reservedFrame frame p).locals.size=frame.locals.size:=by
  simp [reservedFrame,Array.set!,h0,(Array.getElem?_eq_some_iff.mp h1).2,h2,
    show 1<frame.locals.size by omega,show 3<frame.locals.size by omega]

@[simp] theorem reservedFrame_inst(frame:CallFrame)(p:Layout):
    (reservedFrame frame p).inst=frame.inst:=by simp only[reservedFrame]

@[simp] theorem reservedFrame_arity(frame:CallFrame)(p:Layout):
    (reservedFrame frame p).arity=frame.arity:=by simp only[reservedFrame]

@[simp] theorem reservedFrame_height(frame:CallFrame)(p:Layout):
    (reservedFrame frame p).height=frame.height:=by simp only[reservedFrame]

@[simp] theorem reservedFrame_labels(frame:CallFrame)(p:Layout):
    (reservedFrame frame p).labels=frame.labels:=by simp only[reservedFrame]

theorem packed_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:5≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out161))
    (h1:frame.locals[1]?=some (.i32 p.pointer))(h2:frame.locals[2]?=some (.i32 p.length)):
    (packedFrame frame p q).locals[0]?=some (.i32 p.out161) ∧
    (packedFrame frame p q).locals[1]?=some (.i32 p.pointer) ∧
    (packedFrame frame p q).locals[2]?=some (.i32 p.length) ∧
    (packedFrame frame p q).locals[3]?=some (.i32 (scratch p)) ∧
    (packedFrame frame p q).locals[4]?=some (.i64 (packedValue p q)) ∧
    (packedFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,packedFrame,Array.set!,h0,(Array.getElem?_eq_some_iff.mp h1).2,h2,
    show 1<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

@[simp] theorem packedFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedFrame frame p q).inst=frame.inst:=by simp only[reservedFrame,packedFrame]

@[simp] theorem packedFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedFrame frame p q).arity=frame.arity:=by simp only[reservedFrame,packedFrame]

@[simp] theorem packedFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedFrame frame p q).height=frame.height:=by simp only[reservedFrame,packedFrame]

@[simp] theorem packedFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (packedFrame frame p q).labels=frame.labels:=by simp only[reservedFrame,packedFrame]

theorem final_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:5≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out161))
    (_h1:frame.locals[1]?=some (.i32 p.pointer))(h2:frame.locals[2]?=some (.i32 p.length)):
    (finalFrame frame p q).locals[0]?=some (.i32 p.out161) ∧
    (finalFrame frame p q).locals[1]?=some (.i32 (tagValue p q)) ∧
    (finalFrame frame p q).locals[2]?=some (.i32 p.length) ∧
    (finalFrame frame p q).locals[3]?=some (.i32 (scratch p)) ∧
    (finalFrame frame p q).locals[4]?=some (.i64 (packedValue p q)) ∧
    (finalFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,packedFrame,finalFrame,Array.set!,h0,h2,
    show 1<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

@[simp] theorem finalFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).inst=frame.inst:=by simp only[reservedFrame,packedFrame,finalFrame]

@[simp] theorem finalFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).arity=frame.arity:=by simp only[reservedFrame,packedFrame,finalFrame]

@[simp] theorem finalFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).height=frame.height:=by simp only[reservedFrame,packedFrame,finalFrame]

@[simp] theorem finalFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).labels=frame.labels:=by simp only[reservedFrame,packedFrame,finalFrame]
end WNear.Proofs.StateDecodeBorshRead
