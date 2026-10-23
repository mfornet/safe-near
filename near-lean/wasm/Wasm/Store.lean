import Wasm.Memory

/-!
# The store

Section 4.2 of the specification: all instances live in one store, addressed
by index. Functions are either Wasm functions of a module instance in the
same store or host functions. The store is parametric in the host state `H`,
which only host functions inspect.

Hosts are described by `HostModule`: a set of named functions, globals,
tables and memories that `Link.allocateHost` turns into a module instance
whose exports imports can resolve to, exactly like a Wasm module's.
-/

namespace Wasm

/-- What a host function returns: values or a trap, plus the host state and
the caller's memory (the memory it was given), both possibly updated. -/
inductive HostOutcome (H : Type) where
  | «return» (values : List Value) (host : H) (mem : Option Memory)
  | trap (reason : Trap) (host : H) (mem : Option Memory)

/-- A host function sees the host state, the calling module's first memory
(if it has one) and the arguments, and nothing else. -/
structure HostFn (H : Type) where
  type : FuncType
  call : H → Option Memory → List Value → HostOutcome H

inductive FuncInst (H : Type) where
  /-- A Wasm function of the module instance at `inst` in the store. -/
  | wasm (type : FuncType) (inst : Nat) (code : Func)
  | host (fn : HostFn H)

def FuncInst.type : FuncInst H → FuncType
  | .wasm t _ _ => t
  | .host fn => fn.type

structure TableInst where
  elemType : RefType
  elems : Array Ref
  max : Option Nat
deriving Inhabited

structure GlobalInst where
  type : GlobalType
  value : Value
deriving Inhabited

/-- An element segment instance; dropped segments are empty. -/
structure ElemInst where
  elems : Array Ref
deriving Inhabited

/-- A data segment instance; dropped segments are empty. -/
structure DataInst where
  bytes : ByteArray
deriving Inhabited

inductive ExternVal where
  | func (addr : Nat)
  | table (addr : Nat)
  | mem (addr : Nat)
  | global (addr : Nat)
deriving Repr, DecidableEq, Inhabited

/-- A module instance: the store addresses of everything the module's index
spaces name, and its exports. -/
structure ModuleInst where
  types : Array FuncType := #[]
  funcAddrs : Array Nat := #[]
  tableAddrs : Array Nat := #[]
  memAddrs : Array Nat := #[]
  globalAddrs : Array Nat := #[]
  elemAddrs : Array Nat := #[]
  dataAddrs : Array Nat := #[]
  exports : Array (String × ExternVal) := #[]
deriving Inhabited

def ModuleInst.export? (inst : ModuleInst) (name : String) : Option ExternVal :=
  (inst.exports.find? (·.1 == name)).map (·.2)

structure Store (H : Type) where
  funcs : Array (FuncInst H) := #[]
  tables : Array TableInst := #[]
  mems : Array Memory := #[]
  globals : Array GlobalInst := #[]
  elems : Array ElemInst := #[]
  datas : Array DataInst := #[]
  modules : Array ModuleInst := #[]
  host : H

namespace Store

def empty (host : H) : Store H := { host }

def allocFunc (s : Store H) (f : FuncInst H) : Store H × Nat :=
  ({ s with funcs := s.funcs.push f }, s.funcs.size)

def allocTable (s : Store H) (t : TableInst) : Store H × Nat :=
  ({ s with tables := s.tables.push t }, s.tables.size)

def allocMem (s : Store H) (m : Memory) : Store H × Nat :=
  ({ s with mems := s.mems.push m }, s.mems.size)

def allocGlobal (s : Store H) (g : GlobalInst) : Store H × Nat :=
  ({ s with globals := s.globals.push g }, s.globals.size)

def allocElem (s : Store H) (e : ElemInst) : Store H × Nat :=
  ({ s with elems := s.elems.push e }, s.elems.size)

def allocData (s : Store H) (d : DataInst) : Store H × Nat :=
  ({ s with datas := s.datas.push d }, s.datas.size)

def allocModule (s : Store H) (m : ModuleInst) : Store H × Nat :=
  ({ s with modules := s.modules.push m }, s.modules.size)

def setModule (s : Store H) (i : Nat) (m : ModuleInst) : Store H :=
  { s with modules := s.modules.set! i m }

/-- The first memory of a module instance, which host functions receive. -/
def memOf (s : Store H) (inst : ModuleInst) : Option Memory :=
  inst.memAddrs[0]?.bind (s.mems[·]?)

def setMemOf (s : Store H) (inst : ModuleInst) (m : Memory) : Store H :=
  match inst.memAddrs[0]? with
  | some addr => { s with mems := s.mems.set! addr m }
  | none => s

end Store

/-- A host as a module: what it exports, by name. -/
structure HostModule (H : Type) where
  funcs : List (String × HostFn H) := []
  globals : List (String × GlobalType × Value) := []
  tables : List (String × TableType) := []
  mems : List (String × MemType) := []

end Wasm
