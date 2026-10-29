import Bridge.Functions.ToStrPay

/-!
# `begin_panic` (664) down to the hook's trap, unconditionally

`PanicBegin.f664_spec` with its `ToStr` premise discharged by `ToStrPay.toStr_pay`: the host
panics with `panicText msg file line col`, the message `(m, l)` holding `msg`, the location `loc`
holding `(file, flen, line, col)` with the file's bytes `fileB`. What `to_string` reads and the
heap it allocates in are in `D0 = toStrEnv … ∗ Fr` (`Fr` anything else the caller passes down).

`f664_full`: for any `&'static str` message, file, line and column below `10^4`; the text's bounds
(`HsGlobal`: the sink's at most `J` growths for `B = |panicText …|`), its UTF-8 validity and the
host's log limits are hypotheses. `f664_requiresPositive` and `f664_depositTooSmall` are the two
`require!`s of `near_deposit` (`src/w_near.rs:15:9` and `:20:13`), where the text is valid UTF-8 and
is the model's `Panic.message` (`PanicText.requiresPositiveDeposit_text`, `depositTooSmall_text`).

Cost: `cost664 cfg (costTS cfg F J B) (panicText …) h`.

The message path (`expect_failed` 879, `core::panicking::panic` 853) is `PanicFmtFull` (`f879_unc`,
`f853_unc`): `PanicFmt` keeps the `Arguments`' word at `a + 12` that 887 and 826 copy, and
`PanicEntries.f879_full` routes the `Arguments` through 826 (`GetSpec`'s `G` to `G'`).
-/

namespace WNear.Binary.PanicBeginFull

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.PanicStr (panicSlot panicCode panicked)
open WNear.Binary.PanicHook (ToStr)
open WNear.Binary.PanicBegin (panicCode' env infoD cost664 f664_spec payloadCells)
open WNear.Binary.PanicText (panicText)
open WNear.Binary.HookSink (HsGlobal)
open WNear.Binary.ToStrPay (toStrEnv codeTS costTS toStr_pay)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`std::panicking::begin_panic::<&str>(m, l, loc)`** (664) with the near-sdk hook installed: a
trap, the host panicked with `panicText msg file line col`. -/
theorem f664_full (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 33 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp m l loc lpc : UInt32) (hm0 : m ≠ 0) (S : Nat) (hS : 432 ≤ S) (hsp : S + 112 ≤ sp.toNat)
    (hsp2 : sp.toNat ≤ 2 ^ 32 - 16) (hal : sp.toNat % 8 = 0)
    (file flen line col idx : UInt32) (msg fileB : List UInt8) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F J : Nat)
    (HG : HsGlobal maxP L0 F J (panicText msg fileB line.toNat col.toNat).length)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0) (Fr : IProp GF)
    (hlen : (panicText msg fileB line.toNat col.toNat).length < 2 ^ 32)
    (hutf : validUtf8 (panicText msg fileB line.toNat col.toNat) = true) (h : NearState)
    (hfit : LogFits h (panicText msg fileB line.toNat col.toNat).length)
    (hov : h.extCosts.cost "read_memory_byte" * (panicText msg fileB line.toNat col.toNat).length < 2 ^ 64) :
    A 662 ↪[wf] FuncInst.wasm types[0]! inst f662 ∗ A 663 ↪[wf] FuncInst.wasm types[0]! inst f663 ∗
      A 888 ↪[wf] FuncInst.wasm types[32]! inst f888 ∗ panicCode' e inst mi A n mx ∗ codeTS n maxP inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f664 Cg
        (fun args => iprop(⌜args = [.i32 m, .i32 l, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112 - S) (S + 112) ∗
          env n ta A lpc iprop(toStrEnv n ta A maxP hl live F idx m loc file flen line col msg fileB ∗ Fr) h))
        (fun _ => cost664 cfg (costTS cfg F J (panicText msg fileB line.toNat col.toNat).length)
          (panicText msg fileB line.toNat col.toNat) h)
        (fun _ _ => iprop(False)) (fun _ => panicked Cg h (panicText msg fileB line.toNat col.toNat)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h32 : (sp - 16 - 16).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h16] <;> omega
  have h48 : (sp - 16 - 16 - 16).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h32] <;> omega
  have h80 : (sp - 16 - 16 - 16 - 32).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have h112 : (sp - 16 - 16 - 16 - 32 - 32).toNat = sp.toNat - 112 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h80] <;> omega
  have hip : (sp - 16 - 16 - 16 - 32 + 16).toNat = sp.toNat - 64 := by
    simp [UInt32.toNat_add, h80]; omega
  have hpos : 0 < (panicText msg fileB line.toNat col.toNat).length := by
    have : (PanicText.b "panicked at ").length = 12 := by decide +kernel
    simp only [panicText, List.length_append]; omega
  iintro ⟨#F662, #F663, #F888, #Hc', #Hts⟩
  iapply (f664_spec cfg lim d type inst mi e A n g ta mx hm (by omega) Cg gt sp m l loc lpc hm0 S (by omega) hsp hal
    iprop(toStrEnv n ta A maxP hl live F idx m loc file flen line col msg fileB ∗ Fr)
    (costTS cfg F J (panicText msg fileB line.toNat col.toNat).length)
    (panicText msg fileB line.toNat col.toNat) hpos hlen hutf h hfit hov)
  iframe F662 F663 F888 Hc'
  iunfold infoD
  iapply (toStr_pay cfg lim (d + 6) inst mi A n g ta hm (by omega) Cg gt (sp - 16 - 16 - 16 - 32 - 32)
    (sp - 16 - 16 - 16 - 32 + 16) (sp - 16 - 16 - 16 + 8) m l loc file flen line col idx S hS (by omega)
    (by omega) (by omega) hloc msg fileB hmsg hml hfl hfile hline hcol maxP hl L0 live F J HG hl0 hl1 hlL Fr)
  iexact Hts

/-! ## `near_deposit`'s two `require!`s -/

open WNear.Binary.PanicText (requiresPositive depositTooSmall wnearRs requiresPositiveDeposit_valid
  depositTooSmall_valid decDigits_15 decDigits_9 decDigits_20 decDigits_13)

theorem requiresPositive_text_length : (panicText requiresPositive wnearRs (15 : UInt32).toNat
    (9 : UInt32).toNat).length = 68 := by
  rw [show (15 : UInt32).toNat = 15 from rfl, show (9 : UInt32).toNat = 9 from rfl, panicText, decDigits_15,
    decDigits_9]
  decide +kernel

theorem depositTooSmall_text_length : (panicText depositTooSmall wnearRs (20 : UInt32).toNat
    (13 : UInt32).toNat).length = 56 := by
  rw [show (20 : UInt32).toNat = 20 from rfl, show (13 : UInt32).toNat = 13 from rfl, panicText, decDigits_20,
    decDigits_13]
  decide +kernel

/-- The sink's bounds for a text of at most 128 bytes: at most five growths. -/
theorem hsGlobal_128 {maxP L0 F B : Nat} (hF : 1 ≤ F) (hB : B ≤ 128) (hL1 : L0 + 6 * 65536 ≤ 2 ^ 32)
    (hL2 : L0 + 5 * 65536 ≤ maxP * 65536) : HsGlobal maxP L0 F 5 B :=
  ⟨hF, by decide, by simp; omega, by omega, hL1, hL2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`require!(amount > 0, "Requires positive attached deposit")`** in `near_deposit`
(`src/w_near.rs:15:9`): 664 on `(1050492, 34)` at the `Location` 1050540; the host panicked with the
text `PanicText.requiresPositiveDeposit_text` identifies as `Panic.message .requiresPositiveDeposit`. -/
theorem f664_requiresPositive (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 33 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp lpc idx : UInt32) (S : Nat) (hS : 432 ≤ S) (hsp : S + 112 ≤ sp.toNat)
    (hsp2 : sp.toNat ≤ 2 ^ 32 - 16) (hal : sp.toNat % 8 = 0)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : 1 ≤ F) (hL1 : L0 + 6 * 65536 ≤ 2 ^ 32)
    (hL2 : L0 + 5 * 65536 ≤ maxP * 65536) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0) (Fr : IProp GF)
    (h : NearState) (hfit : LogFits h 68) (hov : h.extCosts.cost "read_memory_byte" * 68 < 2 ^ 64) :
    A 662 ↪[wf] FuncInst.wasm types[0]! inst f662 ∗ A 663 ↪[wf] FuncInst.wasm types[0]! inst f663 ∗
      A 888 ↪[wf] FuncInst.wasm types[32]! inst f888 ∗ panicCode' e inst mi A n mx ∗ codeTS n maxP inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f664 Cg
        (fun args => iprop(⌜args = [.i32 1050492, .i32 34, .i32 1050540]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112 - S) (S + 112) ∗
          env n ta A lpc iprop(toStrEnv n ta A maxP hl live F idx 1050492 1050540 1050526 13 15 9
            requiresPositive wnearRs ∗ Fr) h))
        (fun _ => cost664 cfg (costTS cfg F 5 68) (panicText requiresPositive wnearRs 15 9) h)
        (fun _ _ => iprop(False)) (fun _ => panicked Cg h (panicText requiresPositive wnearRs 15 9)) := by
  have hT := requiresPositive_text_length
  have S := f664_full (GF := GF) cfg lim d type inst mi e A n g ta mx hm hd Cg gt sp 1050492 34 1050540 lpc
    (by decide) S hS hsp hsp2 hal 1050526 13 15 9 idx requiresPositive wnearRs (by decide) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) (by decide) maxP hl L0 live F 5
    (hsGlobal_128 hF (by rw [hT]; decide) hL1 hL2) hl0 hl1 hlL Fr (by rw [hT]; decide)
    requiresPositiveDeposit_valid h (by rw [hT]; exact hfit) (by rw [hT]; exact hov)
  rw [hT] at S
  exact S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`require!(…, "ERR_DEPOSIT_TOO_SMALL")`** in `near_deposit` (`src/w_near.rs:20:13`): 664 on
`(1050556, 21)` at the `Location` 1050580; the text is `Panic.message .depositTooSmall`
(`PanicText.depositTooSmall_text`). -/
theorem f664_depositTooSmall (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 33 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp lpc idx : UInt32) (S : Nat) (hS : 432 ≤ S) (hsp : S + 112 ≤ sp.toNat)
    (hsp2 : sp.toNat ≤ 2 ^ 32 - 16) (hal : sp.toNat % 8 = 0)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : 1 ≤ F) (hL1 : L0 + 6 * 65536 ≤ 2 ^ 32)
    (hL2 : L0 + 5 * 65536 ≤ maxP * 65536) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0) (Fr : IProp GF)
    (h : NearState) (hfit : LogFits h 56) (hov : h.extCosts.cost "read_memory_byte" * 56 < 2 ^ 64) :
    A 662 ↪[wf] FuncInst.wasm types[0]! inst f662 ∗ A 663 ↪[wf] FuncInst.wasm types[0]! inst f663 ∗
      A 888 ↪[wf] FuncInst.wasm types[32]! inst f888 ∗ panicCode' e inst mi A n mx ∗ codeTS n maxP inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f664 Cg
        (fun args => iprop(⌜args = [.i32 1050556, .i32 21, .i32 1050580]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112 - S) (S + 112) ∗
          env n ta A lpc iprop(toStrEnv n ta A maxP hl live F idx 1050556 1050580 1050526 13 20 13
            depositTooSmall wnearRs ∗ Fr) h))
        (fun _ => cost664 cfg (costTS cfg F 5 56) (panicText depositTooSmall wnearRs 20 13) h)
        (fun _ _ => iprop(False)) (fun _ => panicked Cg h (panicText depositTooSmall wnearRs 20 13)) := by
  have hT := depositTooSmall_text_length
  have S := f664_full (GF := GF) cfg lim d type inst mi e A n g ta mx hm hd Cg gt sp 1050556 21 1050580 lpc
    (by decide) S hS hsp hsp2 hal 1050526 13 20 13 idx depositTooSmall wnearRs (by decide) (by decide +kernel)
    (by decide) (by decide +kernel) (by decide) (by decide) (by decide) maxP hl L0 live F 5
    (hsGlobal_128 hF (by rw [hT]; decide) hL1 hL2) hl0 hl1 hlL Fr (by rw [hT]; decide)
    depositTooSmall_valid h (by rw [hT]; exact hfit) (by rw [hT]; exact hov)
  rw [hT] at S
  exact S

end Spec

end WNear.Binary.PanicBeginFull
