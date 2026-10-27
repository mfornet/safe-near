import NearFastVM.Ops
import NearFastVM.Mem
import NearVM.Run

/-!
# The flat instruction stream

A function body is compiled to an `Array Ins`. Structured control is resolved to jumps, and every operand is
addressed by its slot in the frame: the height of the operand stack at each instruction is known statically
(the module is validated), so there is no stack pointer at run time. A frame is `[locals | operands]` in one
`Array UInt32` (a slot is two words; see `ExecCore`).

Field use by operation (`x`, `y`, `z`, `w` are 32 bit, `imm` is 64 bit; all slots are relative to the frame
pointer):

* operations on the operand stack: `x` is the lowest operand slot, which also receives the result
* `const`: `x` destination, `imm` the bits
* `local_get`: `x` destination, `y` the local; `local_set`/`local_tee`: `x` source, `y` the local
* `global_get`: `x` destination, `y` the global; `global_set`: `x` source
* `ldN`/`stN`: `x` the address slot (the loaded value goes there; a store reads its value from `x + 1`),
  `imm` the offset
* `jmp`: `y` target. `br`: `y` target, and when `z > 0` the `z` values at `x` move to `w`
* `br_if`: `x` condition, as `br`; `cost2` is charged when taken. `if_z`: `x` condition, `y` target when zero
* `br_if_z`: `x` condition; falls to the next instruction (a `ret`) when non-zero, else jumps to `y`
* `br_table`: `x` index, `imm` the table; its entries are `Ins` (`br`, or `ret` for a branch out of the function)
* `ret`: `z` results at `x` move to the frame base
* `call`: `imm` the callee's store address, `x` the first argument. `call_indirect`: `x` index slot (the
  arguments are the `z` slots below it), `y` the type index, `w` the table
* `cold`: `imm` indexes `FnCode.colds`, `x` the lowest operand slot, `z` the number of operands
-/

namespace NearFastVM

open Wasm Wasm.Near

instance : Inhabited (FuncInst H) :=
  ⟨.wasm default 0 default⟩

structure Ins where
  op : Op
  cost : UInt64 := 0
  cost2 : UInt64 := 0
  x : UInt32 := 0
  y : UInt32 := 0
  z : UInt32 := 0
  w : UInt32 := 0
  imm : UInt64 := 0
  deriving Inhabited

/-- A compiled function. -/
structure FnCode where
  code : Array Ins
  tables : Array (Array Ins)
  colds : Array Instr
  /-- Number of locals including parameters. -/
  nlocals : Nat
  nparams : Nat
  /-- Slots the frame needs: locals and the deepest operand stack. -/
  frameSlots : Nat
  results : List ValType
  /-- The charge for entering the function (`activationGas`). -/
  activation : Nat
  deriving Inhabited

/-- Everything a run reads and never writes. -/
structure Ctx where
  funcs : Array (FuncInst NearState)
  tables : Array TableInst
  inst : ModuleInst
  /-- The index of `inst` in the store: every function the run enters belongs to it. -/
  instIdx : Nat
  maxDepth : Nat
  regular : Nat
  linBase : Nat
  linUnit : Nat
  hasMem : Bool
  memMax : Option Nat

end NearFastVM
