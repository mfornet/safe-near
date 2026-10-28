import Proofs.StateReadRegisterOuterState
import Proofs.StateDispatchReadCall

/-! The exact actual435 ABI after523's real687 allocation. The original-memory
version records only installed code/selector facts before any guest writes. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic

def readOn (p : Layout) (memory : Memory) : StateDispatchRead.Layout :=
  {mi:=p.mi,globalIndex:=p.globalIndex,memoryIndex:=p.memoryIndex,tableAddress:=p.tableAddress,
   table:=p.table,global:={p.global523 with value:=.i32 (scratch p)},sp:=scratch p,
   interface:=1055020,lookupElement:=p.lookupElement,memory,
   inputRegister:=scratch p+24,inputPointer:=scratch p+32}

def originalReadLayout (p : Layout) := readOn p p.memory
def readInputMemory (p : Layout) := AllocateVectorOuter.finalMemory (actualVector p)
def readLayout (p : Layout) := readOn p (readInputMemory p)
def readOutputMemory (p : Layout) := StateDispatchRead.readMemory (readLayout p) p.bytes
end WNear.Proofs.StateReadRegisterOuter
