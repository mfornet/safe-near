import Bridge.Methods.StaticsNew
import Bridge.Methods.CodeDeposit

/-!
# What `near_deposit` (234) starts with

`memResDep` carves the instantiated memory into the cells `near_deposit` owns, in address order:
912 bytes of stack below 1048576, the interface's vtable words, the panic sites' messages,
locations and file names, the log's pieces, `PanicOnDefault`'s message, the zero `u128`, the
overflow message, the `Display` pieces and arrays, the digit table, the UTF-8 width table, the
heap's head and the hook's and the interface's cells. `tableResDep`/`tableOfDep`: the table entries
`near_deposit` reaches.

`staticsResDep`: `DepositBody234.statics234` with the addresses of `wInst` (`A = id`), the
default hook (`old = 0`), the interface not set up (`k3 = 0`), no panic count (`lpc = 0`), the
three panics' data `DepositPanicsFull.dAll`, wee_alloc's vtable index 123 and the empty heap; and
`PanicOnDefault`'s message.
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (dataWord dataWord_eq)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.PanicDisplay (pk12 pptrA plenA pptrB plenB qp qcp colon)

theorem seg_v32 : seg 1050220 4 = dataWord (1050188 + 32) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v104 : seg 1050292 4 = dataWord (1050188 + 104) := by rw [dataWord_eq _ (by decide)]; rfl

section Mem

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `cut` with the rest of the window as `[a + len, L)`, so that the windows do not nest. -/
theorem cutL {m : Memory} (L n c R a len : Nat) {P Q : IProp GF} (hcR : c + R = L) (hc : c ≤ a)
    (hR : a + len ≤ L) (hP : memR m n a len ⊢ P) (hQ : memR m n (a + len) (L - (a + len)) ⊢ Q) :
    memR m n c R ⊢ P ∗ Q :=
  cut n c R a len hc (by omega) hP (by rwa [show c + R - (a + len) = L - (a + len) by omega])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- The memory's cells `near_deposit` owns, in address order. -/
theorem memResDep {m : Memory} {L : Nat} (hm : MemImage m L) (hL : 1074944 ≤ L) (n : Nat) :
    memR (GF := GF) m n 0 L ⊢
      stk n 1047664 912 ∗ (n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      (n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ (n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗
      (n ↦[wms][ 1050188 + 32 ] dataWord (1050188 + 32) ∗ (n ↦[wms][ 1050188 + 64 ] dataWord (1050188 + 64) ∗
      (n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ (n ↦[wms][ 1050188 + 100 ] dataWord (1050188 + 100) ∗
      (n ↦[wms][ 1050188 + 104 ] dataWord (1050188 + 104) ∗ (n ↦[wms][ 1050188 + 184 ] dataWord (1050188 + 184) ∗
      (n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗ (n ↦[wms][ 1050188 + 196 ] dataWord (1050188 + 196) ∗
      (n ↦[wms][ 1050492 ] PanicText.requiresPositive ∗ (n ↦[wms][ 1050526 ] PanicText.wnearRs ∗
      (n ↦[i32][ 1050540 ] 1050526 ∗ (n ↦[i32][ 1050544 ] 13 ∗ (n ↦[i32][ 1050548 ] 15 ∗ (n ↦[i32][ 1050552 ] 9 ∗
      (n ↦[wms][ 1050556 ] PanicText.depositTooSmall ∗
      (n ↦[i32][ 1050580 ] 1050526 ∗ (n ↦[i32][ 1050584 ] 13 ∗ (n ↦[i32][ 1050588 ] 20 ∗ (n ↦[i32][ 1050592 ] 13 ∗
      (n ↦[wms][ 1050612 ] DepositLog.pDeposit ∗ (n ↦[wms][ 1050620 ] DepositLog.pNear ∗
      (n ↦[i32][ 1050632 ] 1050612 ∗ (n ↦[i32][ 1050636 ] 8 ∗ (n ↦[i32][ 1050640 ] 1050620 ∗
      (n ↦[i32][ 1050644 ] 9 ∗
      (n ↦[wms][ 1050868 ] PanicStr.notInit ∗
      (n ↦[wms][ 1052800 ] List.replicate 8 (0 : UInt8) ∗ (n ↦[wms][ 1052800 + 8 ] List.replicate 8 (0 : UInt8) ∗
      (n ↦[wms][ 1052816 ] PanicText.coreImplRs ∗ (n ↦[wms][ 1053000 ] InternalDepositOverflow.balMsg ∗
      (n ↦[wms][ 1053016 ] PanicText.totalSupplyOverflow ∗
      (n ↦[i32][ 1053040 ] 1052816 ∗ (n ↦[i32][ 1053044 ] 119 ∗ (n ↦[i32][ 1053048 ] 108 ∗
      (n ↦[i32][ 1053052 ] 55 ∗
      (n ↦[i32][ 1054332 ] 1054332 ∗ (n ↦[i32][ 1054336 ] 0 ∗
      (n ↦[i32][ 1055020 ] 116 ∗ (n ↦[i32][ 1055148 ] 118 ∗ (n ↦[i32][ 1057480 ] 123 ∗
      (n ↦[i32][ 1062984 ] 137 ∗ (n ↦[i32][ 1063000 ] 139 ∗ (n ↦[i32][ 1065416 ] 157 ∗
      (n ↦[i32][ 1065692 ] 166 ∗ (n ↦[i32][ 1066376 ] 179 ∗ (n ↦[i32][ 1066740 ] 189 ∗
      (n ↦[i32][ 1070628 ] 1067136 ∗ (n ↦[i32][ 1070632 ] 0 ∗
      (n ↦[wms][ 1070672 ] pk12 ∗ (n ↦[wms][ 1070684 ] qp ∗ (n ↦[wms][ 1070685 ] qcp ∗
      (n ↦[i32][ 1070688 ] pptrA 0 ∗ (n ↦[i32][ 1070692 ] plenA 0 ∗ (n ↦[i32][ 1070696 ] pptrA 1 ∗
      (n ↦[i32][ 1070700 ] plenA 1 ∗
      (n ↦[wms][ 1070704 ] colon ∗
      (n ↦[i32][ 1070708 ] pptrB 0 ∗ (n ↦[i32][ 1070712 ] plenB 0 ∗ (n ↦[i32][ 1070716 ] pptrB 1 ∗
      (n ↦[i32][ 1070720 ] plenB 1 ∗ (n ↦[i32][ 1070724 ] pptrB 2 ∗ (n ↦[i32][ 1070728 ] plenB 2 ∗
      (n ↦[wms][ 1070974 ] FmtDigits.lut ∗ (n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      (n ↦[i32][ 1074896 ] 0 ∗
      (n ↦[i32][ 1074900 ] 0 ∗ (n ↦[i32][ 1074904 ] 0 ∗ (n ↦[i32][ 1074908 ] 0 ∗ (n ↦[i32][ 1074912 ] 0 ∗
      (n ↦[i32][ 1074920 ] 0 ∗ (n ↦[i32][ 1074924 ] 0 ∗ (n ↦[i32][ 1074928 ] 0 ∗ (n ↦[i32][ 1074932 ] 0 ∗
      (n ↦[i32][ 1074936 ] 0 ∗ (n ↦[i32][ 1074940 ] 0 ∗ True
      )))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) := by
  have hL0 := hm.1
  refine cutL L n 0 L 1047664 912 (by omega) (by omega) (by omega)
    ((memR_zero hm n 1047664 912 (Or.inr (by decide)) (by omega)).trans (zero_stk n 1047664 912)) ?_
  refine cutL L n _ _ 1049788 5 (by omega) (by omega) (by omega) (conv_data hm n 1049788 5 (by decide) (by decide) (by omega)
    seg_key rfl) ?_
  refine cutL L n _ _ 1050200 4 (by omega) (by omega) (by omega) (conv_data hm n 1050200 4 (by decide) (by decide) (by omega)
    seg_v12 rfl) ?_
  refine cutL L n _ _ 1050204 4 (by omega) (by omega) (by omega) (conv_data hm n 1050204 4 (by decide) (by decide) (by omega)
    seg_v16 rfl) ?_
  refine cutL L n _ _ 1050220 4 (by omega) (by omega) (by omega) (conv_data hm n 1050220 4 (by decide) (by decide) (by omega)
    seg_v32 rfl) ?_
  refine cutL L n _ _ 1050252 4 (by omega) (by omega) (by omega) (conv_data hm n 1050252 4 (by decide) (by decide) (by omega)
    seg_v64 rfl) ?_
  refine cutL L n _ _ 1050280 4 (by omega) (by omega) (by omega) (conv_data hm n 1050280 4 (by decide) (by decide) (by omega)
    seg_v92 rfl) ?_
  refine cutL L n _ _ 1050288 4 (by omega) (by omega) (by omega) (conv_data hm n 1050288 4 (by decide) (by decide) (by omega)
    seg_v100 rfl) ?_
  refine cutL L n _ _ 1050292 4 (by omega) (by omega) (by omega) (conv_data hm n 1050292 4 (by decide) (by decide) (by omega)
    seg_v104 rfl) ?_
  refine cutL L n _ _ 1050372 4 (by omega) (by omega) (by omega) (conv_data hm n 1050372 4 (by decide) (by decide) (by omega)
    seg_v184 rfl) ?_
  refine cutL L n _ _ 1050376 4 (by omega) (by omega) (by omega) (conv_data hm n 1050376 4 (by decide) (by decide) (by omega)
    seg_v188 rfl) ?_
  refine cutL L n _ _ 1050384 4 (by omega) (by omega) (by omega) (conv_data hm n 1050384 4 (by decide) (by decide) (by omega)
    seg_v196 rfl) ?_
  refine cutL L n _ _ 1050492 34 (by omega) (by omega) (by omega) (conv_data hm n 1050492 34 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050526 13 (by omega) (by omega) (by omega) (conv_data hm n 1050526 13 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050540 4 (by omega) (by omega) (by omega) (conv_data hm n 1050540 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050544 4 (by omega) (by omega) (by omega) (conv_data hm n 1050544 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050548 4 (by omega) (by omega) (by omega) (conv_data hm n 1050548 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050552 4 (by omega) (by omega) (by omega) (conv_data hm n 1050552 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050556 21 (by omega) (by omega) (by omega) (conv_data hm n 1050556 21 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050580 4 (by omega) (by omega) (by omega) (conv_data hm n 1050580 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050584 4 (by omega) (by omega) (by omega) (conv_data hm n 1050584 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050588 4 (by omega) (by omega) (by omega) (conv_data hm n 1050588 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050592 4 (by omega) (by omega) (by omega) (conv_data hm n 1050592 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050612 8 (by omega) (by omega) (by omega) (conv_data hm n 1050612 8 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050620 9 (by omega) (by omega) (by omega) (conv_data hm n 1050620 9 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050632 4 (by omega) (by omega) (by omega) (conv_data hm n 1050632 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050636 4 (by omega) (by omega) (by omega) (conv_data hm n 1050636 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050640 4 (by omega) (by omega) (by omega) (conv_data hm n 1050640 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050644 4 (by omega) (by omega) (by omega) (conv_data hm n 1050644 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1050868 31 (by omega) (by omega) (by omega) (conv_data hm n 1050868 31 (by decide) (by decide) (by omega)
    seg_notInit rfl) ?_
  refine cutL L n _ _ 1052800 8 (by omega) (by omega) (by omega) (conv_data hm n 1052800 8 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1052808 8 (by omega) (by omega) (by omega) (conv_data hm n 1052808 8 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1052816 119 (by omega) (by omega) (by omega) (conv_data hm n 1052816 119 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1053000 16 (by omega) (by omega) (by omega) (conv_data hm n 1053000 16 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1053016 21 (by omega) (by omega) (by omega) (conv_data hm n 1053016 21 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1053040 4 (by omega) (by omega) (by omega) (conv_data hm n 1053040 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1053044 4 (by omega) (by omega) (by omega) (conv_data hm n 1053044 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1053048 4 (by omega) (by omega) (by omega) (conv_data hm n 1053048 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1053052 4 (by omega) (by omega) (by omega) (conv_data hm n 1053052 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1054332 4 (by omega) (by omega) (by omega) (conv_data hm n 1054332 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1054336 4 (by omega) (by omega) (by omega) (conv_data hm n 1054336 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1055020 4 (by omega) (by omega) (by omega) (conv_data hm n 1055020 4 (by decide) (by decide) (by omega)
    seg_key116 rfl) ?_
  refine cutL L n _ _ 1055148 4 (by omega) (by omega) (by omega) (conv_data hm n 1055148 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1057480 4 (by omega) (by omega) (by omega) (conv_data hm n 1057480 4 (by decide) (by decide) (by omega)
    seg_vt rfl) ?_
  refine cutL L n _ _ 1062984 4 (by omega) (by omega) (by omega) (conv_data hm n 1062984 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1063000 4 (by omega) (by omega) (by omega) (conv_data hm n 1063000 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1065416 4 (by omega) (by omega) (by omega) (conv_data hm n 1065416 4 (by decide) (by decide) (by omega)
    seg_157 rfl) ?_
  refine cutL L n _ _ 1065692 4 (by omega) (by omega) (by omega) (conv_data hm n 1065692 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1066376 4 (by omega) (by omega) (by omega) (conv_data hm n 1066376 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1066740 4 (by omega) (by omega) (by omega) (conv_data hm n 1066740 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070628 4 (by omega) (by omega) (by omega) (conv_data hm n 1070628 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070632 4 (by omega) (by omega) (by omega) (conv_data hm n 1070632 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070672 12 (by omega) (by omega) (by omega) (conv_data hm n 1070672 12 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070684 1 (by omega) (by omega) (by omega) (conv_data hm n 1070684 1 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070685 3 (by omega) (by omega) (by omega) (conv_data hm n 1070685 3 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070688 4 (by omega) (by omega) (by omega) (conv_data hm n 1070688 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070692 4 (by omega) (by omega) (by omega) (conv_data hm n 1070692 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070696 4 (by omega) (by omega) (by omega) (conv_data hm n 1070696 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070700 4 (by omega) (by omega) (by omega) (conv_data hm n 1070700 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070704 1 (by omega) (by omega) (by omega) (conv_data hm n 1070704 1 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070708 4 (by omega) (by omega) (by omega) (conv_data hm n 1070708 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070712 4 (by omega) (by omega) (by omega) (conv_data hm n 1070712 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070716 4 (by omega) (by omega) (by omega) (conv_data hm n 1070716 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070720 4 (by omega) (by omega) (by omega) (conv_data hm n 1070720 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070724 4 (by omega) (by omega) (by omega) (conv_data hm n 1070724 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070728 4 (by omega) (by omega) (by omega) (conv_data hm n 1070728 4 (by decide) (by decide) (by omega)
    (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1070974 200 (by omega) (by omega) (by omega) (conv_data hm n 1070974 200 (by decide) (by decide)
    (by omega) seg_lut rfl) ?_
  refine cutL L n _ _ 1071704 256 (by omega) (by omega) (by omega) (conv_data hm n 1071704 256 (by decide) (by decide)
    (by omega) (by decide +kernel) rfl) ?_
  refine cutL L n _ _ 1074896 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074896 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074900 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074900 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074904 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074904 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074908 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074908 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074912 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074912 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074920 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074920 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074924 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074924 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074928 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074928 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074932 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074932 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074936 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074936 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cutL L n _ _ 1074940 4 (by omega) (by omega) (by omega) (conv_zero hm n 1074940 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  exact true_intro

/-- The table entries `near_deposit` reaches through `call_indirect`. -/
def tableResDep (ta : Nat) : IProp GF :=
  iprop(ta ↦[wt][ 3 ] Ref.func 870 ∗ ta ↦[wt][ 5 ] Ref.func 901 ∗ ta ↦[wt][ 6 ] Ref.func 179 ∗
    ta ↦[wt][ 38 ] Ref.func 240 ∗ ta ↦[wt][ 39 ] Ref.func 241 ∗ ta ↦[wt][ 43 ] Ref.func 245 ∗
    ta ↦[wt][ 51 ] Ref.func 253 ∗ ta ↦[wt][ 58 ] Ref.func 260 ∗ ta ↦[wt][ 60 ] Ref.func 262 ∗
    ta ↦[wt][ 61 ] Ref.func 263 ∗ ta ↦[wt][ 81 ] Ref.func 283 ∗ ta ↦[wt][ 82 ] Ref.func 284 ∗
    ta ↦[wt][ 84 ] Ref.func 286 ∗ ta ↦[wt][ 104 ] Ref.func 469 ∗ ta ↦[wt][ 106 ] Ref.func 564 ∗
    ta ↦[wt][ 116 ] Ref.func 565 ∗ ta ↦[wt][ 118 ] Ref.func 473 ∗ ta ↦[wt][ 123 ] Ref.func 578 ∗
    ta ↦[wt][ 137 ] Ref.func 679 ∗ ta ↦[wt][ 139 ] Ref.func 661 ∗ ta ↦[wt][ 157 ] Ref.func 759 ∗
    ta ↦[wt][ 166 ] Ref.func 799 ∗ ta ↦[wt][ 179 ] Ref.func 826 ∗ ta ↦[wt][ 189 ] Ref.func 840 ∗
    ta ↦[wt][ 195 ] Ref.func 880 ∗ ta ↦[wt][ 201 ] Ref.func 886 ∗ ta ↦[wt][ 202 ] Ref.func 887)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The table entries `near_deposit` uses, from the start's table cells. -/
theorem tableOfDep : ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ⊢ tableResDep (GF := GF) 0 := by
  have hs : (([3, 5, 6, 38, 39, 43, 51, 58, 60, 61, 81, 82, 84, 104, 106, 116, 118, 123, 137, 139, 157, 166, 179,
      189, 195, 201, 202] : List Nat).map fun i =>
      ((Loc.tableElem 0 i, .ref wTable.elems[i]!) : Loc × Cell NearState)).Sublist tabCells :=
    List.Sublist.map _ (by decide)
  refine (bigSepL_sublist (Φ := fun p : Loc × Cell NearState => iprop(p.1 ↦ₛ p.2)) hs).trans ?_
  simp only [List.map_cons, List.map_nil]
  have e : ∀ i (r : Ref), wTable.elems[i]! = r →
      ((Loc.tableElem 0 i ↦ₛ (.ref wTable.elems[i]! : Cell NearState)) : IProp GF) ⊢ 0 ↦[wt][ i ] r := by
    intro i r hr; rw [hr]; exact .rfl
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H3, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H5, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H6, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H38, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H39, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H43, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H51, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H58, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H60, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H61, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H81, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H82, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H84, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H104, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H106, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H116, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H118, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H123, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H137, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H139, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H157, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H165, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H179, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H189, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H195, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H201, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H202, -⟩
  ihave H3 := e 3 (Ref.func 870) rfl $$ H3
  ihave H5 := e 5 (Ref.func 901) rfl $$ H5
  ihave H6 := e 6 (Ref.func 179) rfl $$ H6
  ihave H38 := e 38 (Ref.func 240) rfl $$ H38
  ihave H39 := e 39 (Ref.func 241) rfl $$ H39
  ihave H43 := e 43 (Ref.func 245) rfl $$ H43
  ihave H51 := e 51 (Ref.func 253) rfl $$ H51
  ihave H58 := e 58 (Ref.func 260) rfl $$ H58
  ihave H60 := e 60 (Ref.func 262) rfl $$ H60
  ihave H61 := e 61 (Ref.func 263) rfl $$ H61
  ihave H81 := e 81 (Ref.func 283) rfl $$ H81
  ihave H82 := e 82 (Ref.func 284) rfl $$ H82
  ihave H84 := e 84 (Ref.func 286) rfl $$ H84
  ihave H104 := e 104 (Ref.func 469) rfl $$ H104
  ihave H106 := e 106 (Ref.func 564) rfl $$ H106
  ihave H116 := e 116 (Ref.func 565) rfl $$ H116
  ihave H118 := e 118 (Ref.func 473) rfl $$ H118
  ihave H123 := e 123 (Ref.func 578) rfl $$ H123
  ihave H137 := e 137 (Ref.func 679) rfl $$ H137
  ihave H139 := e 139 (Ref.func 661) rfl $$ H139
  ihave H157 := e 157 (Ref.func 759) rfl $$ H157
  ihave H165 := e 166 (Ref.func 799) rfl $$ H165
  ihave H179 := e 179 (Ref.func 826) rfl $$ H179
  ihave H189 := e 189 (Ref.func 840) rfl $$ H189
  ihave H195 := e 195 (Ref.func 880) rfl $$ H195
  ihave H201 := e 201 (Ref.func 886) rfl $$ H201
  ihave H202 := e 202 (Ref.func 887) rfl $$ H202
  iunfold tableResDep
  iframe H3 H5 H6 H38 H39 H43 H51 H58 H60 H61 H81 H82 H84 H104 H106 H116 H118 H123 H137 H139 H157 H165 H179
    H189 H195 H201 H202

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **The statics of `near_deposit`** from the instantiated memory (`MemImage`), its length `len`
and limit 2048, and the table: 912 bytes of stack below 1048576, `statics234` (the default hook,
the interface not set up, no panic count, the three panics' data `dAll`, wee_alloc's vtable index
123, the empty heap) and `PanicOnDefault`'s message. -/
theorem staticsResDep {m : Memory} {L : Nat} (hm : MemImage m L) (hL : 1074944 ≤ L) (n ta len : Nat)
    (hl1 : len % 65536 = 0) (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ tableResDep ta ⊢
      stk n 1047664 912 ∗
        DepositBody234.statics234 n ta id 0 0 0 (DepositPanicsFull.dAll n ta id) 123 2048 len ∗
        n ↦[wms][ 1050868 ] PanicStr.notInit := by
  refine (sep_mono_left (memResDep hm hL n)).trans ?_
  iintro ⟨⟨STK, KEY, V12, V16, V32, V64, V92, V100, V104, V184, V188, V196, MP, FW, L0, L4, L8, L12, MS, S0, S4,
    S8, S12, PD, PN, G0, G4, G8, G12, NI, Z0, Z8, FC, BM, MT, U0, U4, U8, U12, W0, W4, K116, K118, K123, K137, K139,
    K157, K165, K179, K189, R0, R4, PK, QP, QCP, A0, A4, A8, A12, CO, B0, B4, B8, B12, B16, B20, LUT, UW, HEAD,
    I0, I4, I8, I12, H0, H4, H8, H12, X0, X4, -⟩, HL, #HM, HT⟩
  iunfold tableResDep at HT
  icases HT with ⟨T3, T5, T6, T38, T39, T43, T51, T58, T60, T61, T81, T82, T84, T104, T106, T116, T118, T123,
    T137, T139, T157, T165, T179, T189, T195, T201, T202⟩
  ihave HPS : PanicStr.panicSlot (GF := GF) n ta id $$ [V100 T60]
  · iapply PanicStr.panicSlot_of n ta id
    isplitl [V100]
    · iexact V100
    · simp only [id]; iexact T60
  ihave HDs : EnvGetters.dslot (GF := GF) n ta id $$ [V64 T51]
  · iapply EnvGetters.dslot_of n ta id
    isplitl [V64]
    · iexact V64
    · simp only [id]; iexact T51
  ihave HPs : EnvPredecessor.pslot (GF := GF) n ta id $$ [V32 T43]
  · iapply EnvPredecessor.pslot_of n ta id
    isplitl [V32]
    · iexact V32
    · simp only [id]; iexact T43
  ihave HHs : StorageHasKey.hslot (GF := GF) n ta id $$ [V196 T84]
  · iapply StorageHasKey.hslot_of n ta id
    isplitl [V196]
    · iexact V196
    · simp only [id]; iexact T84
  ihave HWs : StorageWrite.wslot (GF := GF) n ta id $$ [V184 T81]
  · iapply StorageWrite.wslot_of n ta id
    isplitl [V184]
    · iexact V184
    · simp only [id]; iexact T81
  ihave HLs : LogStr.lslot (GF := GF) n ta id $$ [V104 T61]
  · iapply LogStr.lslot_of n ta id
    isplitl [V104]
    · iexact V104
    · simp only [id]; iexact T61
  ihave HEAD := memBytes_addr (a := 1074896) (b := AllocInv.headAddr) rfl $$ HEAD
  ihave Hinv := AllocInv.heapInv_init n 2048 len hl1 hl0 hl2 $$ [HEAD HL]
  · iframe HEAD HL HM
  ihave Hinv := AllocInv.heapInv_mono n 2048 len [] 0 1 (by decide) $$ Hinv
  ihave HDp : DepositPanicsFull.dAll (GF := GF) n ta id $$ [MP FW L0 L4 L8 L12 MS S0 S4 S8 S12 FC MT U0 U4 U8 U12
      W0 W4 K139 K157 K165 R0 R4 PK QP QCP A0 A4 A8 A12 CO B0 B4 B8 B12 B16 B20 T3 T104 T139 T157 T165 T195 T201
      T202]
  · iunfold DepositPanicsFull.dAll
    isplit
    · iunfold DepositPanicsFull.dPos, DepositPanicsFull.d664, DepositPanicsFull.XPm, DepositPanicsFull.XBm
      simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, id]
      iframe MP FW L0 L4 L8 L12 K139 K157 PK QP QCP A0 A4 A8 A12 CO B0 B4 B8 B12 B16 B20 T3 T104 T139 T157 T195
        T201 W0 W4
    isplit
    · iunfold DepositPanicsFull.dSmall, DepositPanicsFull.d664, DepositPanicsFull.XPm, DepositPanicsFull.XBm
      simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, id]
      iframe MS FW S0 S4 S8 S12 K139 K157 PK QP QCP A0 A4 A8 A12 CO B0 B4 B8 B12 B16 B20 T3 T104 T139 T157 T195
        T201 W0 W4
    · iunfold DepositPanicsFull.dSup, GetFmt.getData, DepositPanicsFull.hookEnvMm, DepositPanicsFull.XBm
      simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, id]
      iframe MT FC U0 U4 U8 U12 R0 R4 K165 K157 PK QP QCP A0 A4 A8 A12 CO B0 B4 B8 B12 B16 B20 T3 T104 T157 T165
        T195 T202 W0 W4
  iframe STK NI
  iunfold DepositBody234.statics234, DepositBody234.hookX, SetupPanicHook.hookCells,
    SetBlockchainInterface.blockchainInterfaceCells, FtTotalSupply.vtab, AllocFirstFit.vt, DepositTail.tailStat,
    DepositTail.logStat, InternalDeposit.zeroAt
  simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, id]
  iframe H12 H0 H4 H8 K116 T116 T106 I0 I4 I8 I12 V16 T39 V92 T58 V188 T82 V12 T38 X0 X4 K118 T118 K137 T137
    K179 T179 HDs HPs HHs HWs HLs HPS HDp BM Z0 Z8 G0 G4 G8 G12 T5 T6 K189 T189 LUT PD PN UW K123 T123 Hinv KEY

end Mem

end WNear.Binary.InitialState
