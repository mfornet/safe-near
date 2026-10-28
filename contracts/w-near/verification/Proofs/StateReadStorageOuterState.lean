import Proofs.StateReadRegisterOuterResult
import Proofs.StateDispatchStorageCall
import Proofs.AllocateSetupGrowthCanonical

/-! Original f548 inputs and its exact high-then-low key-record setup. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends toRegisterOuter : StateReadRegisterOuter.Layout where
  sp548 : UInt32
  global548 : GlobalInst
  out548 : UInt32
  keyPtr : UInt32
  keyLen : UInt32
  address459 : Nat
  address523 : Nat
  address498 : Nat

def scratch (p : Layout) := p.sp548-32
def highMemory (p : Layout) := writeI32 p.memory ((scratch p).toNat+12) p.keyLen
def setupMemory (p : Layout) := writeI32 (highMemory p) ((scratch p).toNat+8) p.keyPtr

def storageLayout (p : Layout) : StateDispatchStorage.Layout :=
  {mi:=p.mi,globalIndex:=p.globalIndex,memoryIndex:=p.memoryIndex,
   tableAddress:=p.tableAddress,table:=p.table,global:={p.global548 with value:=.i32 (scratch p)},
   sp:=scratch p,interface:=1055020,lookupElement:=p.lookupElement,
   memory:=setupMemory p,input:=scratch p+8}
def storageMemory (p : Layout) := StateDispatchLength.finalMemory (storageLayout p)
def registerTemplate (p : Layout) : StateReadRegisterOuter.Layout :=
  {p.toRegisterOuter with memory:=storageMemory p}
def registerSaved (p : Layout) := AllocateRetry.savedMemory (registerTemplate p).toRetry
def registerDelta (p : Layout) := AllocateGrowth.delta (AllocateRetry.growthLayout p.toRetry)
def actualRegister (p : Layout) : StateReadRegisterOuter.Layout :=
  {registerTemplate p with grown:=AllocateSetupGrowth.grownMemory (registerSaved p) (registerDelta p).toNat}

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def highStore (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (reserved s op p) op 3) p.memoryIndex ((scratch p).toNat+12) p.memory p.keyLen
def setupStore (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (highStore s op p) op 3) p.memoryIndex ((scratch p).toNat+8) (highMemory p) p.keyPtr
def storageArguments (s : Store NearState) (op : Nat) (p : Layout) := paid (setupStore s op p) op 4
def stored (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  StateDispatchStorage.callAfter cfg (storageArguments s cfg.regularOpCost p) (storageLayout p) ctx key p.bytes

def reservedFrame (frame : CallFrame) (p : Layout) :=
  {frame with locals:=frame.locals.set! 3 (.i32 (scratch p))}
end WNear.Proofs.StateReadStorageOuter
