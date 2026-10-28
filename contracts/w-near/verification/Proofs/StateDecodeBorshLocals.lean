import Proofs.StateDecodeBorshPhases
import Proofs.StateDecodeBorshCache
import Proofs.StateDecodeBorshCacheVector

/-! Every deployed425 local write is in bounds for its eight-local frame.
Cached frame aliases preserve control metadata and retain the literal snapshots. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64 prefixMemory prefixPacked prefixLength savedPrefixMemory wideMemory wideFirstMemory wideSecondMemory savedWideMemory wideHigh wideLow narrowMemory narrowHighMemory savedNarrowMemory vectorLength vectorHighMemory vectorPacked cachedMemory usageValue

theorem cachePrefixFrame_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    cachePrefixFrame (reservedFrame frame p) (prefixMemory p q) (scratch p)=prefixFrame frame p q:=by simp only[cachePrefixFrame,StateDecodeScalar.loaded64Frame,prefixFrame,prefixPacked]

theorem prefixSavedFrame_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    prefixSavedFrame (prefixFrame frame p q) (scratch p)=savedPrefixFrame frame p q:=rfl

theorem cacheWideFrame_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    cacheWideFrame (savedPrefixFrame frame p q) (savedWideMemory p q) (scratch p)=wideFrame frame p q:=by simp only[cacheWideFrame,cacheWideFirstFrame,StateDecodeScalar.loaded64Frame,wideFrame,wideHigh,wideLow]

theorem vectorCachedFrame_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    vectorCachedFrame (wideFrame frame p q) (savedNarrowMemory p q) (scratch p)=vectorFrame frame p q:=by
  simp only[vectorCachedFrame,vectorHighFrame,vectorFrame,vectorLength,vectorPacked,cacheVectorHighMemory,vectorHighMemory]

theorem cacheNarrowFrame_eq(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    cacheNarrowFrame (vectorFrame frame p q) (cachedMemory p q) (scratch p)=finalFrame frame p q:=by
  simp only[cacheNarrowFrame,StateDecodeScalar.loaded64Frame,finalFrame,usageValue]

theorem reserved_locals(frame:CallFrame)(p:Layout)
    (hs:8≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out425))(h1:frame.locals[1]?=some (.i32 p.slice)):
    (reservedFrame frame p).locals[0]?=some (.i32 p.out425) ∧
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

theorem prefix_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:8≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out425))(h1:frame.locals[1]?=some (.i32 p.slice)):
    (prefixFrame frame p q).locals[0]?=some (.i32 p.out425) ∧
    (prefixFrame frame p q).locals[1]?=some (.i32 p.slice) ∧
    (prefixFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (prefixFrame frame p q).locals[3]?=some (.i64 (prefixPacked p q)) ∧
    (prefixFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,prefixFrame,Array.set!,h0,h1,
    show 2<frame.locals.size by omega,show 3<frame.locals.size by omega]

@[simp] theorem prefixFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixFrame frame p q).inst=frame.inst:=by simp only[prefixFrame,reservedFrame_inst]

@[simp] theorem prefixFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixFrame frame p q).arity=frame.arity:=by simp only[prefixFrame,reservedFrame_arity]

@[simp] theorem prefixFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixFrame frame p q).height=frame.height:=by simp only[prefixFrame,reservedFrame_height]

@[simp] theorem prefixFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (prefixFrame frame p q).labels=frame.labels:=by simp only[prefixFrame,reservedFrame_labels]

theorem savedPrefix_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:8≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out425))(h1:frame.locals[1]?=some (.i32 p.slice)):
    (savedPrefixFrame frame p q).locals[0]?=some (.i32 p.out425) ∧
    (savedPrefixFrame frame p q).locals[1]?=some (.i32 p.slice) ∧
    (savedPrefixFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (savedPrefixFrame frame p q).locals[3]?=some (.i64 (prefixPacked p q)) ∧
    (savedPrefixFrame frame p q).locals[4]?=some (.i32 (scratch p+68)) ∧
    (savedPrefixFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,prefixFrame,savedPrefixFrame,Array.set!,h0,h1,
    show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

@[simp] theorem savedPrefixFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (savedPrefixFrame frame p q).inst=frame.inst:=by simp only[savedPrefixFrame,prefixFrame_inst]

@[simp] theorem savedPrefixFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (savedPrefixFrame frame p q).arity=frame.arity:=by simp only[savedPrefixFrame,prefixFrame_arity]

@[simp] theorem savedPrefixFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (savedPrefixFrame frame p q).height=frame.height:=by simp only[savedPrefixFrame,prefixFrame_height]

@[simp] theorem savedPrefixFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (savedPrefixFrame frame p q).labels=frame.labels:=by simp only[savedPrefixFrame,prefixFrame_labels]

theorem wide_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:8≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out425))(h1:frame.locals[1]?=some (.i32 p.slice)):
    (wideFrame frame p q).locals[0]?=some (.i32 p.out425) ∧
    (wideFrame frame p q).locals[1]?=some (.i32 p.slice) ∧
    (wideFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (wideFrame frame p q).locals[3]?=some (.i64 (wideHigh p q)) ∧
    (wideFrame frame p q).locals[4]?=some (.i32 (scratch p+68)) ∧
    (wideFrame frame p q).locals[5]?=some (.i64 (wideLow p q)) ∧
    (wideFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,prefixFrame,savedPrefixFrame,wideFrame,Array.set!,h0,h1,
    show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega,show 5<frame.locals.size by omega]

@[simp] theorem wideFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideFrame frame p q).inst=frame.inst:=by simp only[wideFrame,savedPrefixFrame_inst]

@[simp] theorem wideFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideFrame frame p q).arity=frame.arity:=by simp only[wideFrame,savedPrefixFrame_arity]

@[simp] theorem wideFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideFrame frame p q).height=frame.height:=by simp only[wideFrame,savedPrefixFrame_height]

@[simp] theorem wideFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (wideFrame frame p q).labels=frame.labels:=by simp only[wideFrame,savedPrefixFrame_labels]

theorem vector_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:8≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out425))(_h1:frame.locals[1]?=some (.i32 p.slice)):
    (vectorFrame frame p q).locals[0]?=some (.i32 p.out425) ∧
    (vectorFrame frame p q).locals[1]?=some (.i32 (vectorLength p q)) ∧
    (vectorFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (vectorFrame frame p q).locals[3]?=some (.i64 (wideHigh p q)) ∧
    (vectorFrame frame p q).locals[4]?=some (.i32 (scratch p+68)) ∧
    (vectorFrame frame p q).locals[5]?=some (.i64 (wideLow p q)) ∧
    (vectorFrame frame p q).locals[6]?=some (.i64 (vectorPacked p q)) ∧
    (vectorFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,prefixFrame,savedPrefixFrame,wideFrame,vectorFrame,Array.set!,h0,
    show 1<frame.locals.size by omega,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega,show 5<frame.locals.size by omega,show 6<frame.locals.size by omega]

@[simp] theorem vectorFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (vectorFrame frame p q).inst=frame.inst:=by simp only[vectorFrame,wideFrame_inst]

@[simp] theorem vectorFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (vectorFrame frame p q).arity=frame.arity:=by simp only[vectorFrame,wideFrame_arity]

@[simp] theorem vectorFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (vectorFrame frame p q).height=frame.height:=by simp only[vectorFrame,wideFrame_height]

@[simp] theorem vectorFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (vectorFrame frame p q).labels=frame.labels:=by simp only[vectorFrame,wideFrame_labels]

theorem final_locals(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hs:8≤frame.locals.size)(h0:frame.locals[0]?=some (.i32 p.out425))(_h1:frame.locals[1]?=some (.i32 p.slice)):
    (finalFrame frame p q).locals[0]?=some (.i32 p.out425) ∧
    (finalFrame frame p q).locals[1]?=some (.i32 (vectorLength p q)) ∧
    (finalFrame frame p q).locals[2]?=some (.i32 (scratch p)) ∧
    (finalFrame frame p q).locals[3]?=some (.i64 (wideHigh p q)) ∧
    (finalFrame frame p q).locals[4]?=some (.i32 (scratch p+68)) ∧
    (finalFrame frame p q).locals[5]?=some (.i64 (wideLow p q)) ∧
    (finalFrame frame p q).locals[6]?=some (.i64 (vectorPacked p q)) ∧
    (finalFrame frame p q).locals[7]?=some (.i64 (usageValue p q)) ∧
    (finalFrame frame p q).locals.size=frame.locals.size:=by
  simp [reservedFrame,prefixFrame,savedPrefixFrame,wideFrame,vectorFrame,finalFrame,Array.set!,h0,
    show 1<frame.locals.size by omega,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega,show 5<frame.locals.size by omega,show 6<frame.locals.size by omega,show 7<frame.locals.size by omega]

@[simp] theorem finalFrame_inst(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).inst=frame.inst:=by simp only[finalFrame,vectorFrame_inst]

@[simp] theorem finalFrame_arity(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).arity=frame.arity:=by simp only[finalFrame,vectorFrame_arity]

@[simp] theorem finalFrame_height(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).height=frame.height:=by simp only[finalFrame,vectorFrame_height]

@[simp] theorem finalFrame_labels(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).labels=frame.labels:=by simp only[finalFrame,vectorFrame_labels]
end WNear.Proofs.StateDecodeBorsh
