import Bridge.Functions.FmtDigits
import Bridge.Functions.Interface
import Model.Calls

/-!
# The text of a Rust panic through near-sdk's hook, and the data it is made of

`<PanicInfo as Display>::fmt` (885) in Rust 1.51 writes

```
"panicked at "  then  "'" {msg} "', "  then  {file} ":" {line} ":" {col}
```

(`write_str("panicked at ")`, then `write!("'{}', ", message or payload)`, then
`<Location as Display>`: `write!("{}:{}:{}", file, line, col)`, the line and column through
`<u32 as Display>`, i.e. `fmt_u64` (936) on the zero-extended value, no padding). `panicText`
is that text on bytes, the decimal digits `FmtDigits.decDigits`.

The model's texts are `rustPanic msg location = s!"panicked at '{msg}', {location}"`
(`Model/Calls.lean`); the instances below check that the binary's data for `near_deposit`'s two
`require!`s and `internal_deposit`'s `expect("Total supply overflow")` give exactly
`Panic.message` (`requiresPositiveDeposit_text`, `depositTooSmall_text`,
`totalSupplyOverflow_text`).

## The data

* the pieces of 885: `"panicked at "` (1070672, 12), `"'"` (1070684, 1), `"', "` (1070685, 3) in
  the array 1070688 `[("'", 1), ("', ", 3)]`; the `Location`'s array 1070708
  `[("", 0), (":", 1), (":", 1)]`, `":"` at 1070704;
* near_deposit's `require!(amount > 0, "Requires positive attached deposit")`: 664 on
  `(1050492, 34)` at the `Location` 1050540 `("src/w_near.rs" (1050526, 13), 15, 9)`;
  `require!(…, "ERR_DEPOSIT_TOO_SMALL")`: 664 on `(1050556, 21)` at 1050580 `(…, 20, 13)`;
* `internal_deposit`'s `checked_add(…).expect("Total supply overflow")`: `Option::expect` (363)
  calls `expect_failed` (879) on `(1053016, 21)` with the `Location` 1053040
  `(".../near-contract-standards-3.1.0/src/fungible_token/core_impl.rs" (1052816, 119), 108, 55)`;
  the other site (`internal_withdraw`, 119:55) passes 1053096.
-/

namespace WNear.Binary.PanicText

open Wasm Wasm.Near
open WNear.Binary.FmtDigits (decDigits digit)

/-- The bytes of a string. -/
abbrev b (s : String) : List UInt8 := s.toUTF8.toList

/-- **The panic text** of `<PanicInfo as Display>` on the message `msg` at `file:line:col`. -/
def panicText (msg file : List UInt8) (line col : Nat) : List UInt8 :=
  b "panicked at " ++ (b "'" ++ msg ++ b "', ") ++ (file ++ b ":" ++ decDigits line ++ b ":" ++ decDigits col)

/-- The `len` bytes of the data segment at `addr`. -/
def dataBytes (addr len : Nat) : List UInt8 :=
  (List.range len).map fun k => wNearSource.read (159306 + (addr - 1048576) + k)

/-! ## The pieces -/

theorem panickedAt_data : dataBytes 1070672 12 = b "panicked at " := by decide +kernel
theorem quote_data : dataBytes 1070684 1 = b "'" := by decide +kernel
theorem quoteComma_data : dataBytes 1070685 3 = b "', " := by decide +kernel
theorem colon_data : dataBytes 1070704 1 = b ":" := by decide +kernel

/-- The words of a `Location` / pieces array in the data segment. -/
def dataWords (addr k : Nat) : List UInt32 :=
  (List.range k).map fun i => UInt32.ofNat (Wasm.Memory.decodeLE (dataBytes (addr + 4 * i) 4))

/-- 885's message pieces: `[("'", 1), ("', ", 3)]`. -/
theorem msgPieces_data : dataWords 1070688 4 = [1070684, 1, 1070685, 3] := by decide +kernel

/-- The `Location`'s pieces: `[("", 0), (":", 1), (":", 1)]` (the empty piece at 1067136). -/
theorem locPieces_data : dataWords 1070708 6 = [1067136, 0, 1070704, 1, 1070704, 1] := by decide +kernel

/-! ## `near_deposit` -/

def wnearRs : List UInt8 := b "src/w_near.rs"

theorem wnearRs_data : dataBytes 1050526 13 = wnearRs := by decide +kernel

def requiresPositive : List UInt8 := b "Requires positive attached deposit"

theorem requiresPositive_data : dataBytes 1050492 34 = requiresPositive := by decide +kernel

/-- The `Location` 1050540: `src/w_near.rs:15:9`. -/
theorem requiresPositive_loc : dataWords 1050540 4 = [1050526, 13, 15, 9] := by decide +kernel

def depositTooSmall : List UInt8 := b "ERR_DEPOSIT_TOO_SMALL"

theorem depositTooSmall_data : dataBytes 1050556 21 = depositTooSmall := by decide +kernel

/-- The `Location` 1050580: `src/w_near.rs:20:13`. -/
theorem depositTooSmall_loc : dataWords 1050580 4 = [1050526, 13, 20, 13] := by decide +kernel

/-! ## `internal_deposit`'s total supply -/

def coreImplRs : List UInt8 :=
  b "/usr/local/cargo/registry/src/github.com-1ecc6299db9ec823/near-contract-standards-3.1.0/src/fungible_token/core_impl.rs"

set_option maxRecDepth 10000 in
theorem coreImplRs_data : dataBytes 1052816 119 = coreImplRs := by decide +kernel

def totalSupplyOverflow : List UInt8 := b "Total supply overflow"

theorem totalSupplyOverflow_data : dataBytes 1053016 21 = totalSupplyOverflow := by decide +kernel

/-- The `Location` 1053040 (`internal_deposit`): `core_impl.rs:108:55`. -/
theorem totalSupplyOverflow_loc : dataWords 1053040 4 = [1052816, 119, 108, 55] := by decide +kernel

/-- The `Location` 1053096 (`internal_withdraw`): `core_impl.rs:119:55`. -/
theorem totalSupplyUnderflow_loc : dataWords 1053096 4 = [1052816, 119, 119, 55] := by decide +kernel

/-! ## Against the model -/

theorem decDigits_9 : decDigits 9 = b "9" := by simp [decDigits, digit]; decide +kernel
theorem decDigits_13 : decDigits 13 = b "13" := by simp [decDigits, digit]; decide +kernel
theorem decDigits_15 : decDigits 15 = b "15" := by simp [decDigits, digit]; decide +kernel
theorem decDigits_20 : decDigits 20 = b "20" := by simp [decDigits, digit]; decide +kernel
theorem decDigits_55 : decDigits 55 = b "55" := by simp [decDigits, digit]; decide +kernel
theorem decDigits_108 : decDigits 108 = b "108" := by simp [decDigits, digit]; decide +kernel
theorem decDigits_119 : decDigits 119 = b "119" := by simp [decDigits, digit]; decide +kernel

/-- `require!(amount > 0, "Requires positive attached deposit")` in `near_deposit`. -/
theorem requiresPositiveDeposit_text :
    utf8String (panicText requiresPositive wnearRs 15 9) = Panic.message .requiresPositiveDeposit := by
  rw [panicText, decDigits_15, decDigits_9]; decide +kernel

/-- `require!(…, "ERR_DEPOSIT_TOO_SMALL")` in `near_deposit`. -/
theorem depositTooSmall_text :
    utf8String (panicText depositTooSmall wnearRs 20 13) = Panic.message .depositTooSmall := by
  rw [panicText, decDigits_20, decDigits_13]; decide +kernel

/-- `expect("Total supply overflow")` in `internal_deposit`. -/
theorem totalSupplyOverflow_text :
    utf8String (panicText totalSupplyOverflow coreImplRs 108 55) = Panic.message .totalSupplyOverflow := by
  rw [panicText, decDigits_108, decDigits_55]; decide +kernel

/-- `expect("Total supply overflow")` in `internal_withdraw`. -/
theorem totalSupplyUnderflow_text :
    utf8String (panicText totalSupplyOverflow coreImplRs 119 55) = Panic.message .totalSupplyUnderflow := by
  rw [panicText, decDigits_119, decDigits_55]; decide +kernel

/-- The texts are valid UTF-8 (the `panic_utf8` host's premise). -/
theorem requiresPositiveDeposit_valid : validUtf8 (panicText requiresPositive wnearRs 15 9) = true := by
  rw [panicText, decDigits_15, decDigits_9]; decide +kernel

theorem depositTooSmall_valid : validUtf8 (panicText depositTooSmall wnearRs 20 13) = true := by
  rw [panicText, decDigits_20, decDigits_13]; decide +kernel

theorem totalSupplyOverflow_valid : validUtf8 (panicText totalSupplyOverflow coreImplRs 108 55) = true := by
  rw [panicText, decDigits_108, decDigits_55]; decide +kernel

end WNear.Binary.PanicText
