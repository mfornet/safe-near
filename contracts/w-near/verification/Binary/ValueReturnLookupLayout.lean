import Binary.ValueReturnLayout
import Binary.ValueReturnThreadLocal

namespace WNear.Binary.ValueReturnLookupLayout
open Wasm
set_option maxRecDepth 10000

theorem lookup_element : (wNearModule.elems[0]!).init[115]? = some [.ref_func 565] := by kernel_rfl

theorem source_word : (List.range 4).map (fun i => wNearSource.read (159306 + 6444 + i)) =
    [116, 0, 0, 0] := by kernel_rfl

theorem data_read (i : Nat) (hi : i < 4) :
    dataInit.data[6444 + i]! = wNearSource.read (159306 + 6444 + i) := by
  have hb : 6444 + i < 26319 := by omega
  simp only [dataInit, getElem!_def, Array.getElem?_ofFn, hb, ↓reduceDIte, Nat.add_assoc]

theorem data_word : (List.range 4).map (fun i => dataInit.data[6444 + i]!) = [116, 0, 0, 0] := by
  rw [← source_word]
  apply List.map_congr_left
  intro i hi
  exact data_read i (List.mem_range.mp hi)
end WNear.Binary.ValueReturnLookupLayout
