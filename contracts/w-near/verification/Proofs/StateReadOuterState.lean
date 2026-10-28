import Proofs.StateReadStorageOuterCall
import Proofs.StateReadOuterCopies
import Proofs.StateReadOuterPackedValues
import Proofs.PackWordsCall
import Proofs.StateDecodeBorshReadCall
import Proofs.VectorDropInsertCall
import Proofs.VectorDropInsertResult

/-! Pure sequential phases of219's selected present/decode-success path.
The decoder/allocation/release records below are structural templates only.
Their actual native domains must be DERIVED from the original storage data;
no future Native, code lookup or execution outcome is a field here. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends toStorage:StateReadStorageOuter.Layout where
  decoderTemplate:StateDecodeBorshRead.Layout
  allocationTemplate:StateDecodeVectorCopy.Layout
  releaseTemplate:DeallocateCore.Layout
  vectorTemplate:VectorDropPositive.Layout
  sp219:UInt32
  global219:GlobalInst
  out219:UInt32
  address548:Nat
  address779:Nat
  address161:Nat
  address951:Nat
  address68:Nat
  address237:Nat
  address582:Nat

def scratch(p:Layout):=p.sp219-96
def storageMemory(p:Layout):=StateReadStorageOuter.finalMemory p.toStorage
def copiedMemory(p:Layout):=copiedStorageMemory (storageMemory p) (scratch p)
def packedMemory(p:Layout):=preparedStorageMemory (storageMemory p) (scratch p)

def actualDecoder(p:Layout):StateDecodeBorshRead.Layout:=
  {p.decoderTemplate with toWrapper:={p.decoderTemplate.toWrapper with toBorsh:={p.decoderTemplate.toBorsh with toPrefixWrapper:={p.decoderTemplate.toPrefixWrapper with toPrefix:={p.decoderTemplate.toPrefix with memory:=packedMemory p,pointer:=readI32 (packedMemory p) (scratch p).toNat,length:=readI32 (packedMemory p) ((scratch p).toNat+4)}}}}}
def decodeCount(p:Layout):=StateDecodeBorshRead.count (actualDecoder p)
def actualAllocation(p:Layout):StateDecodeVectorCopy.Layout:=
  {p.allocationTemplate with source:=StateDecodePrefix.payloadPointer (actualDecoder p).toPrefix,toVector:={p.allocationTemplate.toVector with toRaw:={p.allocationTemplate.toRaw with toPositive:={p.allocationTemplate.toPositive with memory:=packedMemory p,size:=decodeCount p}}}}
def decodedMemory(p:Layout):=StateDecodeBorshRead.finalMemory (actualDecoder p) (actualAllocation p)
def outputMemory(p:Layout):=ForwardCopyMemory.forward (decodedMemory p) p.out219.toNat (scratch p+48).toNat 40

def actualVector(p:Layout):VectorDropPositive.Layout:=
  {p.vectorTemplate with memory:=outputMemory p,vector:=scratch p+24}
/-- The release record is read AFTER the caller's40-byte result copy. Its
original-domain bridge therefore has to protect it from any caller-output alias. -/
def releaseBase(p:Layout):DeallocateCore.Layout:=
  {p.releaseTemplate with memory:=outputMemory p,pointer:=VectorDropPositive.pointer (actualVector p),length:=VectorDropPositive.capacity (actualVector p),alignment:=1,header:=VectorDropPositive.pointer (actualVector p)+4294967288,previousAddress:=VectorDropPositive.pointer (actualVector p)+4294967292}
def actualRelease(p:Layout):DeallocateCore.Layout:=
  {releaseBase p with previous:=Deallocate.previous (DeallocateCore.zeroMemory (releaseBase p)) (releaseBase p).previousAddress}
def finalMemory(p:Layout):=DeallocateInsert.finalMemory (actualRelease p)

def reserved(s:Store NearState)(op:Nat)(p:Layout):=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def storageArguments(s:Store NearState)(op:Nat)(p:Layout):=paid (reserved s op p) op 5
def stored(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  StateReadStorageOuter.callAfter cfg (storageArguments s cfg.regularOpCost p) p.toStorage ctx key
def presenceChecked(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  paid (stored cfg s p ctx key) cfg.regularOpCost 3
def storageCopied(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  copiedStorage (presenceChecked cfg s p ctx key) cfg.regularOpCost p.memoryIndex (storageMemory p) (scratch p)
def packArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  paid (storageCopied cfg s p ctx key) cfg.regularOpCost 4
def packed(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  PackWordsCall.callAfter (packArguments cfg s p ctx key) cfg.regularOpCost p.memoryIndex (scratch p) (scratch p+24) (copiedMemory p)
def decodeArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  paid (packed cfg s p ctx key) cfg.regularOpCost 7
def decoded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  StateDecodeBorshRead.callAfter cfg (decodeArguments cfg s p ctx key) (actualDecoder p) (actualAllocation p)
def decodeGuarded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  paid (decoded cfg s p ctx key) cfg.regularOpCost 5
def copyArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  paid (decodeGuarded cfg s p ctx key) cfg.regularOpCost 7
def outputCopied(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  UnwrapStateCopyEntry.callAfter (copyArguments cfg s p ctx key) cfg.regularOpCost p.memoryIndex p.out219 (scratch p+48) (decodedMemory p) 40
def outputDropped(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  paid (outputCopied cfg s p ctx key) cfg.regularOpCost 1
def releaseArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  paid (outputDropped cfg s p ctx key) cfg.regularOpCost 3
def released(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  VectorDropInsert.callAfter (releaseArguments cfg s p ctx key) cfg.regularOpCost (actualRelease p)
def restored(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  setGlobal (paid (released cfg s p ctx key) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp219)
def after(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  chargedStore (restored cfg s p ctx key) cfg.regularOpCost

def bodyCost(p:Layout):=StateReadStorageOuter.bodyCost p.toStorage+18*(decodeCount p).toNat+6054
def bodySteps(p:Layout):=StateReadStorageOuter.bodySteps p.toStorage+17*(decodeCount p).toNat+5419
def fee(cfg:WasmConfig)(s:Store NearState)(p:Layout)(ctx:NearInterface.Context)(key:List UInt8):=
  StateReadStorageOuter.fee cfg s p.toStorage ctx key

def reservedFrame(frame:CallFrame)(p:Layout):={frame with locals:=frame.locals.set! 1 (.i32 (scratch p))}

@[simp] theorem actualDecoder_memory(p:Layout):(actualDecoder p).memory=packedMemory p:=by rfl
@[simp] theorem actualDecoder_pointer(p:Layout):(actualDecoder p).pointer=readI32 (packedMemory p) (scratch p).toNat:=by rfl
@[simp] theorem actualDecoder_length(p:Layout):(actualDecoder p).length=readI32 (packedMemory p) ((scratch p).toNat+4):=by rfl
@[simp] theorem actualAllocation_memory(p:Layout):(actualAllocation p).memory=packedMemory p:=by rfl
@[simp] theorem actualAllocation_size(p:Layout):(actualAllocation p).size=decodeCount p:=by rfl
@[simp] theorem actualRelease_memory(p:Layout):(actualRelease p).memory=outputMemory p:=by rfl
@[simp] theorem actualRelease_pointer(p:Layout):(actualRelease p).pointer=VectorDropPositive.pointer (actualVector p):=by rfl
@[simp] theorem actualRelease_length(p:Layout):(actualRelease p).length=VectorDropPositive.capacity (actualVector p):=by rfl
@[simp] theorem reservedFrame_inst(frame:CallFrame)(p:Layout):(reservedFrame frame p).inst=frame.inst:=by rfl
@[simp] theorem reservedFrame_arity(frame:CallFrame)(p:Layout):(reservedFrame frame p).arity=frame.arity:=by rfl
@[simp] theorem reservedFrame_height(frame:CallFrame)(p:Layout):(reservedFrame frame p).height=frame.height:=by rfl
@[simp] theorem reservedFrame_labels(frame:CallFrame)(p:Layout):(reservedFrame frame p).labels=frame.labels:=by rfl
end WNear.Proofs.StateReadOuter
