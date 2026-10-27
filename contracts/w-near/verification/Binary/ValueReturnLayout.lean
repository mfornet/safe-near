import Binary.ValueReturnLeaf

/-! Actual static data and element entries used by the SDK return vtable.
These source facts do not assume initialized-memory or table lookup results. -/
namespace WNear.Binary.ValueReturnLayout
open Wasm
set_option maxRecDepth 10000

theorem element_count : wNearModule.elems.size = 1 := by kernel_rfl

theorem element_offset : (wNearModule.elems[0]!).mode = .active 0 [.i32_const 1] := by kernel_rfl

/-- The active segment begins at one, so its entry57 initializes table slot58. -/
theorem return_element : (wNearModule.elems[0]!).init[57]? = some [.ref_func 260] := by kernel_rfl

/-- The four source bytes at vtable1050188 + slot92 encode table index58. -/
theorem source_word : (List.range 4).map (fun i => wNearSource.read (159306 + 1704 + i)) =
    [58, 0, 0, 0] := by kernel_rfl

theorem data_read (i : Nat) (hi : i < 4) :
    dataInit.data[1704 + i]! = wNearSource.read (159306 + 1704 + i) := by
  have hb : 1704 + i < 26319 := by omega
  simp only [dataInit, getElem!_def, Array.getElem?_ofFn, hb, ↓reduceDIte, Nat.add_assoc]

/-- Recover the same word in the actual deployed data initializer without
materializing its26KB array in the kernel. -/
theorem data_word : (List.range 4).map (fun i => dataInit.data[1704 + i]!) = [58, 0, 0, 0] := by
  rw [← source_word]
  apply List.map_congr_left
  intro i hi
  exact data_read i (List.mem_range.mp hi)

end WNear.Binary.ValueReturnLayout
