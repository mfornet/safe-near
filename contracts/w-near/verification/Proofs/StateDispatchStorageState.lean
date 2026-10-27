import Proofs.StateDispatchLengthState
import Proofs.StateDispatchStorageBorrow
import Proofs.StateReadStorageFrame
import Proofs.StateDispatchPrefixHost
import Proofs.StateDispatchHosts
import Proofs.StateDispatchBorrow


/-! Original resources and deterministic accepted phases of deployed f440. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] StateDispatchLength.acquired StateDispatchLength.high StateDispatchLength.low

abbrev Layout := StateDispatchLength.Layout
abbrev scratch := StateDispatchLength.scratch
abbrev acquiredMemory := StateDispatchLength.acquiredMemory
abbrev highMemory := StateDispatchLength.highMemory
abbrev borrowed := StateDispatchLength.borrowed
abbrev lowMemory := StateDispatchLength.lowMemory
abbrev selected := StateDispatchLength.selected
abbrev receiver := StateDispatchLength.receiver
abbrev vtable := StateDispatchLength.vtable
def element (p : Layout) := readI32 (lowMemory p) ((vtable p).toNat + 188)
def keyLen (p : Layout) := ValueReturnDispatch.packed32 (lowMemory p) (p.input.toNat + 4)
def keyPtr (p : Layout) := ValueReturnDispatch.packed32 (lowMemory p) p.input.toNat
abbrev counter := StateDispatchLength.counter
abbrev acquired := StateDispatchLength.acquired
abbrev high := StateDispatchLength.high
abbrev low := StateDispatchLength.low

def checked (s : Store NearState) (op : Nat) (p : Layout) :=
  ValueReturnOuter.nonnullAfter (paid (paid (low s op p) op 2) op 6) op
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (checked s op p) op 10

def fee (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8) :=
  StorageReadCalls.cost ⟨lowMemory p,s.host⟩ ctx.trie (keyLen p) (keyPtr p) 0 key value

def returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key value : List UInt8) :=
  StateReadStorage.callAfter cfg (arguments s cfg.regularOpCost p) p.mi ctx.trie (keyLen p) (keyPtr p) 0 key value

abbrev acquiredFrame := StateDispatchLength.acquiredFrame
def copiedFrame (frame : CallFrame) (p : Layout) :=
  let cf := {acquiredFrame frame p with locals := (acquiredFrame frame p).locals.set! 0 (.i32 (borrowed p))}
  {cf with locals := cf.locals.set! 3 (.i64 0)}
def argumentFrame (frame : CallFrame) (p : Layout) :=
  {copiedFrame frame p with locals := (copiedFrame frame p).locals.set! 0 (.i32 (selected p))}

structure Code (s : Store NearState) (p : Layout) (inst extra : Nat) : Prop where
  prefixCode : StateDispatchPrefix.Code s p.toLayout inst
  nonnullIndex : p.mi.funcAddrs[430]? = some 430
  nonnullFunction : s.funcs[430]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction)
  releaseIndex : p.mi.funcAddrs[431]? = some 431
  releaseFunction : s.funcs[431]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.releaseFunction)
  swapIndex : p.mi.funcAddrs[672]? = some 672
  swapFunction : s.funcs[672]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction)
  returnIndex : p.mi.funcAddrs[432]? = some 432
  returnFunction : s.funcs[432]? = some (.wasm WNear.Binary.StateDispatch.returnSignature inst WNear.Binary.StateDispatch.returnFunction)
  storageElement : p.table.elems[(element p).toNat]? = some (.func 284)
  storageType : p.mi.types[6]? = some WNear.Binary.StateRead.storageForwardSignature
  storageIndex : p.mi.funcAddrs[284]? = some 284
  storageFunction : s.funcs[284]? = some (.wasm WNear.Binary.StateRead.storageForwardSignature inst WNear.Binary.StateRead.storageForwardFunction)
  hostIndex : p.mi.funcAddrs[43]? = some 43
  hostFunction : s.funcs[43]? = some (.host (metered extra "storage_read" storageReadFn).toHostFn)

structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame) (callers : List CallFrame) (p : Layout) (extra : Nat) : Prop where
  code : Code s p frame.inst extra
  prefixReady : StateDispatchPrefix.Ready s limits frame callers p.toLayout 2
  inputLocal : frame.locals[1]? = some (.i32 p.input)
  localSize : 5 ≤ frame.locals.size
  highBound : (scratch p).toNat + 16 ≤ (acquiredMemory p).byteSize
  lowBound : (scratch p).toNat + 12 ≤ (highMemory p).byteSize
  selectBound : (borrowed p).toNat + 4 ≤ (lowMemory p).byteSize
  selectedNonzero : selected p ≠ 0
  cellBound : (selected p).toNat + 8 ≤ (lowMemory p).byteSize
  inputBound : p.input.toNat + 8 ≤ (lowMemory p).byteSize
  vtableBound : (vtable p).toNat + 192 ≤ (lowMemory p).byteSize
  releaseBound : ((scratch p + 8) ||| 4).toNat + 4 ≤ (lowMemory p).byteSize
  counterBound : (counter p).toNat + 4 ≤ (lowMemory p).byteSize

 theorem Code.transport (s t : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) (hf : t.funcs = s.funcs) (hm : t.modules = s.modules) (ht : t.tables = s.tables) : Code t p inst extra := by
  refine ⟨h.prefixCode.transport s t p.toLayout inst hf hm ht,h.nonnullIndex,?_,h.releaseIndex,?_,h.swapIndex,?_,h.returnIndex,?_,
    h.storageElement,h.storageType,h.storageIndex,?_,h.hostIndex,?_⟩ <;> rw [hf]
  · exact h.nonnullFunction
  · exact h.releaseFunction
  · exact h.swapFunction
  · exact h.returnFunction
  · exact h.storageFunction
  · exact h.hostFunction


/-- Gas and profiling do not participate in canonical storage-read resources. -/
theorem ready_of_host_mask (s t : NearState) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (len ptr reg : UInt64) (key value : List UInt8)
    (he : {t with gas := s.gas, gasProfile := s.gasProfile} = s)
    (hr : StorageReadCalls.Ready ⟨memory,s⟩ ctx raw storage len ptr reg key value) :
    StorageReadCalls.Ready ⟨memory,t⟩ ctx raw storage len ptr reg key value := by
  have h : StorageReadCalls.Ready ⟨memory,{t with gas := s.gas,gasProfile := s.gasProfile}⟩ ctx raw storage len ptr reg key value := by rw [he]; exact hr
  exact ⟨h.wf,h.raw_eq,h.represents,h.nodes,h.accounting,h.key_read,h.key_limit,h.value_read,h.register_limit,h.proof⟩

private theorem cost_mask (s t : NearState) (memory : Memory)
    (initial : _root_.Near.TrieOverlay.State) (len ptr reg : UInt64) (key value : List UInt8) :
    StorageReadCalls.cost ⟨memory,{t with gas := s.gas,gasProfile := s.gasProfile}⟩ initial len ptr reg key value =
    StorageReadCalls.cost ⟨memory,t⟩ initial len ptr reg key value := rfl

theorem cost_of_host_mask (s t : NearState) (memory : Memory)
    (initial : _root_.Near.TrieOverlay.State) (len ptr reg : UInt64) (key value : List UInt8)
    (he : {t with gas := s.gas,gasProfile := s.gasProfile} = s) :
    StorageReadCalls.cost ⟨memory,t⟩ initial len ptr reg key value =
    StorageReadCalls.cost ⟨memory,s⟩ initial len ptr reg key value := by
  have h := congrArg (fun h => StorageReadCalls.cost ⟨memory,h⟩ initial len ptr reg key value) he
  exact (cost_mask s t memory initial len ptr reg key value).symm.trans h

end WNear.Proofs.StateDispatchStorage
