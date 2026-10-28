import Bridge.Methods.InitialState

/-!
# The data `new` (290) reads

The two panic messages of `new` (`#[near_bindgen]`'s deposit check and `#[init]`'s
`state_exists` check), the second `b"STATE"` (`state_exists`), the `"a"` that
`measure_account_storage_usage` repeats and the `0u128` it inserts, as the data segment holds them
(`seg`).
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near

/-- `"Method new doesn't accept deposit"`. -/
def depositMsg : List UInt8 :=
  [77, 101, 116, 104, 111, 100, 32, 110, 101, 119, 32, 100, 111, 101, 115, 110, 39, 116, 32, 97, 99, 99, 101,
    112, 116, 32, 100, 101, 112, 111, 115, 105, 116]

/-- `"The contract has already been initialized"`. -/
def initMsg : List UInt8 :=
  [84, 104, 101, 32, 99, 111, 110, 116, 114, 97, 99, 116, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100,
    121, 32, 98, 101, 101, 110, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 100]

theorem seg_deposit : seg 1050899 33 = depositMsg := by decide
theorem seg_init : seg 1050932 41 = initMsg := by decide
theorem seg_key2 : seg 1056468 5 = StateRead.stateKey := by rw [← seg_key]; decide
theorem seg_a : seg 1052792 1 = [97] := by decide
theorem seg_zero128 : seg 1052800 16 = List.replicate 16 0 := by decide

theorem depositMsg_length : depositMsg.length = 33 := rfl
theorem initMsg_length : initMsg.length = 41 := rfl
theorem depositMsg_valid : validUtf8 depositMsg = true := by decide
theorem initMsg_valid : validUtf8 initMsg = true := by decide

theorem depositMsg_utf8String : utf8String depositMsg = "Method new doesn't accept deposit" := by
  decide +kernel

theorem initMsg_utf8String : utf8String initMsg = "The contract has already been initialized" := by
  decide +kernel

end WNear.Binary.InitialState
