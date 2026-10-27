import Binary.Instance
import Binary.Code.Part05
import Binary.Code.Part08
import Binary.Code.Part09
import Binary.Code.Part10
import Binary.Code.Part12
import NearLogic.Tactic.Control
import NearLogic.Call
import NearLogic.Hosts.Registers
import Bridge.Functions.SetBlockchainInterface

/-!
# The installed blockchain interface

`set_blockchain_interface` (`SetBlockchainInterface.lean`) leaves the
thread-local `BLOCKCHAIN_INTERFACE` initialised and holding
`Some(Box<VmBlockchainInterface>)`: the box's data pointer 1 (a zero-sized
box) and vtable 1050188. Every `env::*` wrapper then reaches its host through

* the accessor `__getit` (565, table index 116 at the `LocalKey` 1055020),
  which on the key's state 1 returns the `RefCell` at 1074904 directly
  (`Key::get`, 468, without initialising: `f468_spec`, `f565_spec`);
* `RefCell::borrow` (429, through `BorrowRef::new`, 494, and
  `Cell::replace`, 672): the flag 0 → 1, the `Ref` (value 1074908, flag
  1074904) written out;
* `Option::expect` (430) on the `Some`;
* the method's `call_indirect` through the vtable: the table index at
  `1050188 + offset`, whose entry is a two-instruction trampoline calling
  the host import;
* the `Ref` dropped (431: the flag back to 0) and `Result::expect` (432) on
  the `Ok` of `try_with`.

The vtable is in the data segment (`dataWord`: the word at an address as the
data segment initialises it, from the binary's bytes). The three methods
covered here:

| method          | vtable offset | table index | trampoline | host import |
|-----------------|---------------|-------------|------------|-------------|
| `register_len`  | 16            | 39          | 241        | 1           |
| `value_return`  | 92            | 58          | 260        | 20          |
| `storage_read`  | 188           | 82          | 284        | 43          |

## The invariant

* `iface n ta A` (owned, handed back by every wrapper spec): the key's word
  116 and its table entry, the cells `blockchainInterfaceCells n 1 0 1
  1050188`, and for each method above the vtable word and its table entry
  (`Ref.func (A i)`, `A` the module's function addresses).
* `ifaceCode` (persistent): the code of 565, 468, the borrow helpers (429,
  494, 672, 430, 431, 432, 433) and the trampolines, the three hosts, the memory
  limit and the instance.
* `IfaceMod mi A n g ta`: the module facts (types, function, memory, global
  and table addresses) the specs use, true of `wInst`.

`iface_of_setup` builds `iface` from `SetBlockchainInterface.post`'s cells
with `(data, vtable) = (1, 1050188)` and the vtable words and table entries.
-/

namespace WNear.Binary.Interface

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-! ## The vtable in the data segment, and the table -/

theorem dataInitK_get (i : Nat) (h : i < 26319) :
    dataInitK.data[i]! = wNearSource.read (159306 + i) := by
  unfold dataInitK
  rw [getElem!_pos _ _ (by simpa using h)]
  simp

/-- The four bytes at `addr` as the data segment (at 1048576) initialises
them. -/
noncomputable def dataWord (addr : Nat) : List UInt8 :=
  (List.range 4).map fun k => dataInitK.data[addr - 1048576 + k]!

theorem dataWord_eq (addr : Nat) (h : addr - 1048576 + 4 ≤ 26319) :
    dataWord addr = (List.range 4).map fun k => wNearSource.read (159306 + (addr - 1048576) + k) := by
  unfold dataWord
  apply List.map_congr_left
  intro k hk
  simp at hk
  rw [dataInitK_get _ (by omega), Nat.add_assoc]

/-- The vtable's header: `drop_in_place` (table index 37), size 0, align 1. -/
theorem vtable_header : dataWord 1050188 = bytes32 37 ∧ dataWord (1050188 + 4) = bytes32 0 ∧
    dataWord (1050188 + 8) = bytes32 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [dataWord_eq _ (by decide)]; decide)

/-- `register_len`: the table index 39. -/
theorem vtable_registerLen : dataWord (1050188 + 16) = bytes32 39 := by
  rw [dataWord_eq _ (by decide)]; decide

/-- `value_return`: the table index 58. -/
theorem vtable_valueReturn : dataWord (1050188 + 92) = bytes32 58 := by
  rw [dataWord_eq _ (by decide)]; decide

/-- `storage_read`: the table index 82. -/
theorem vtable_storageRead : dataWord (1050188 + 188) = bytes32 82 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entries: the trampolines 241, 260, 284, the accessor 565 and
its initialiser 564. -/
theorem wTable_entries : wTable.elems[39]? = some (Ref.func 241) ∧
    wTable.elems[58]? = some (Ref.func 260) ∧ wTable.elems[82]? = some (Ref.func 284) ∧
    wTable.elems[116]? = some (Ref.func 565) ∧ wTable.elems[106]? = some (Ref.func 564) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The trampolines' imports: `register_len` (1), `value_return` (20),
`storage_read` (43), as the instantiated store holds them. -/
theorem wStore_hosts (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[1]? =
        some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "register_len" registerLenFn).toHostFn) ∧
      (wStore cfg h).funcs[20]? =
        some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn) ∧
      (wStore cfg h).funcs[43]? =
        some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "storage_read" storageReadFn).toHostFn) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [wStore, wHosts]

/-! ## The module facts -/

/-- What the specs need of the module instance: its types are the binary's,
function `i` is at address `A i`, memory, global and table 0 at `n`, `g`,
`ta`. -/
structure IfaceMod (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat) : Prop where
  types : mi.types = types
  funcs : ∀ i, i < 955 → mi.funcAddrs[i]? = some (A i)
  mem : mi.memAddrs[0]? = some n
  glob : mi.globalAddrs[0]? = some g
  table : mi.tableAddrs[0]? = some ta

theorem wInst_ifaceMod : IfaceMod wInst id 0 0 0 where
  types := rfl
  funcs i h := by simp [wInst, h]
  mem := rfl
  glob := rfl
  table := rfl

/-! ## The invariant -/

section Inv

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A vtable slot: the table index `idx` at `1050188 + off`, and its entry. -/
def slot (n ta off : Nat) (idx : UInt32) (a : Nat) : IProp GF :=
  iprop(n ↦[i32][ 1050188 + off ] idx ∗ ta ↦[wt][ idx.toNat ] Ref.func a)

/-- **The installed blockchain interface** (owned): the `LocalKey`'s table
index 116 and its entry (the accessor 565), `BLOCKCHAIN_INTERFACE`
initialised and free holding `Some((1, 1050188))`, and the vtable slots of
`register_len`, `value_return` and `storage_read`. -/
def iface (n ta : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(n ↦[i32][ 1055020 ] 116 ∗ ta ↦[wt][ 116 ] Ref.func (A 565) ∗
    blockchainInterfaceCells n 1 0 1 1050188 ∗
    slot n ta 16 39 (A 241) ∗ slot n ta 92 58 (A 260) ∗ slot n ta 188 82 (A 284))

/-- The code the wrappers run through the interface (persistent). -/
def ifaceCode (e : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    IProp GF :=
  iprop(A 565 ↪[wf] FuncInst.wasm types[1]! inst f565 ∗
    A 468 ↪[wf] FuncInst.wasm types[13]! inst f468 ∗
    A 429 ↪[wf] FuncInst.wasm types[31]! inst f429 ∗
    A 494 ↪[wf] FuncInst.wasm types[32]! inst f494 ∗
    A 672 ↪[wf] FuncInst.wasm types[13]! inst f672 ∗
    A 430 ↪[wf] FuncInst.wasm types[13]! inst f430 ∗
    A 431 ↪[wf] FuncInst.wasm types[0]! inst f431 ∗
    A 432 ↪[wf] FuncInst.wasm types[24]! inst f432 ∗
    A 433 ↪[wf] FuncInst.wasm types[0]! inst f433 ∗
    A 241 ↪[wf] FuncInst.wasm types[7]! inst f241 ∗
    A 260 ↪[wf] FuncInst.wasm types[4]! inst f260 ∗
    A 284 ↪[wf] FuncInst.wasm types[6]! inst f284 ∗
    A 1 ↪[wf] FuncInst.host (metered e "register_len" registerLenFn).toHostFn ∗
    A 20 ↪[wf] FuncInst.host (metered e "value_return" valueReturnFn).toHostFn ∗
    A 43 ↪[wf] FuncInst.host (metered e "storage_read" storageReadFn).toHostFn ∗
    n ↪[wmlimit] mx ∗ inst ↪[inst] mi)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (ifaceCode (GF := GF) e inst mi A n mx) := by
  unfold ifaceCode; infer_instance

/-- From `set_blockchain_interface`'s cells, with the box `(1, 1050188)`, and
the three vtable words and table entries. -/
theorem iface_of_setup (n ta : Nat) (A : Nat → Nat) :
    n ↦[i32][ 1055020 ] 116 ∗ ta ↦[wt][ 116 ] Ref.func (A 565) ∗
      blockchainInterfaceCells (GF := GF) n 1 0 1 1050188 ∗
      n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗ ta ↦[wt][ 39 ] Ref.func (A 241) ∗
      n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ ta ↦[wt][ 58 ] Ref.func (A 260) ∗
      n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗ ta ↦[wt][ 82 ] Ref.func (A 284)
      ⊢ iface n ta A := by
  rw [vtable_registerLen, vtable_valueReturn, vtable_storageRead]
  iintro ⟨Hk, Ht, Hc, H1, T1, H2, T2, H3, T3⟩
  iunfold iface, slot
  simp only [UInt32.reduceToNat]
  iframe Hk Ht Hc H1 T1 H2 T2 H3 T3

end Inv

end WNear.Binary.Interface
