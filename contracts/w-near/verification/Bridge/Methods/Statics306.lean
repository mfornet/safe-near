import Bridge.Methods.InitialState
import Bridge.Functions.StorageBalanceBoundsBody

/-!
# What `storage_balance_bounds` (306) starts with: `ft_total_supply`'s statics and the JSON data

`InitialState.memRes0` carves the instantiated memory into the cells `ft_total_supply` owns;
`memRes306` carves it with the struct serializer's data too (`SerdeStruct.boundsData`: the
punctuation `}`, `{`, `,`, `:` at 1048744 and 1048758..1048760, the keys `min` and `max` at
1048824 and 1048827, `:` at 1051834 and the lowercase letters' `ESCAPE` entries at
1061808 + 97). `staticsRes306P` gives `StorageBalanceBoundsBody.statics306` with the panic path's
cells, `staticsRes306` without them.
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (dataWord dataWord_eq dataInitK_get)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)

theorem seg_rbrace : seg 1048744 1 = [125] := by decide
theorem seg_lbrace : seg 1048758 1 = [123] := by decide
theorem seg_comma : seg 1048759 1 = [44] := by decide
theorem seg_colon : seg 1048760 1 = [58] := by decide
theorem seg_min : seg 1048824 3 = SerdeStruct.keyMin := by decide
theorem seg_max : seg 1048827 3 = SerdeStruct.keyMax := by decide
theorem seg_colon2 : seg 1051834 1 = [58] := by decide
set_option maxRecDepth 100000 in
theorem seg_lower : seg 1061905 26 = SerdeStruct.escLower := by decide

section Mem

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells) in
open WNear.Binary.SetupPanicHook (hookCells) in
/-- `memRes0` with the struct serializer's data, in address order. -/
theorem memRes306 {m : Memory} {L : Nat} (hm : MemImage m L) (n : Nat) :
    memR (GF := GF) m n 0 L ⊢
      stk n 1047840 736 ∗ (n ↦[wms][ 1048744 ] [125] ∗ (n ↦[wms][ 1048758 ] [123] ∗
      (n ↦[wms][ 1048759 ] [44] ∗ (n ↦[wms][ 1048760 ] [58] ∗ (n ↦[wms][ 1048824 ] SerdeStruct.keyMin ∗
      (n ↦[wms][ 1048827 ] SerdeStruct.keyMax ∗
      (n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      (n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ (n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗
      (n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ (n ↦[wms][ 1050188 + 100 ] dataWord (1050188 + 100) ∗
      (n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗ (n ↦[wms][ 1050868 ] PanicStr.notInit ∗
      (n ↦[wms][ 1051817 ] [34] ∗ (n ↦[wms][ 1051834 ] [58] ∗
      ((n ↦[i32][ 1051836 ] 1051836 ∗ n ↦[i32][ 1051836 + 4 ] 0) ∗
      (n ↦[i32][ 1055020 ] 116 ∗ (n ↦[i32][ 1057480 ] 123 ∗ (n ↦[wms][ 1061856 ] SerializeStr.esc ∗
      (n ↦[wms][ 1061905 ] SerdeStruct.escLower ∗
      (n ↦[i32][ 1065416 ] 157 ∗ (n ↦[wms][ 1070974 ] FmtDigits.lut ∗ (n ↦[i32][ 1074896 ] 0 ∗
      ((n ↦[i32][ 1074900 ] 0 ∗ n ↦[i32][ 1074900 + 4 ] 0 ∗ n ↦[i32][ 1074900 + 8 ] 0 ∗ n ↦[i32][ 1074900 + 12 ] 0) ∗
      ((n ↦[i32][ 1074920 ] 0 ∗ n ↦[i32][ 1074920 + 4 ] 0 ∗ n ↦[i32][ 1074920 + 8 ] 0 ∗
        n ↦[i32][ 1074920 + 12 ] 0) ∗ True))))))))))))))))))))))))) := by
  have hL := hm.1
  refine cut n 0 L 1047840 736 (by omega) (by omega)
    ((memR_zero hm n 1047840 736 (Or.inr (by decide)) (by omega)).trans (zero_stk n 1047840 736)) ?_
  refine cut n _ _ 1048744 1 (by omega) (by omega) (conv_data hm n 1048744 1 (by decide) (by decide) (by omega)
    seg_rbrace rfl) ?_
  refine cut n _ _ 1048758 1 (by omega) (by omega) (conv_data hm n 1048758 1 (by decide) (by decide) (by omega)
    seg_lbrace rfl) ?_
  refine cut n _ _ 1048759 1 (by omega) (by omega) (conv_data hm n 1048759 1 (by decide) (by decide) (by omega)
    seg_comma rfl) ?_
  refine cut n _ _ 1048760 1 (by omega) (by omega) (conv_data hm n 1048760 1 (by decide) (by decide) (by omega)
    seg_colon rfl) ?_
  refine cut n _ _ 1048824 3 (by omega) (by omega) (conv_data hm n 1048824 3 (by decide) (by decide) (by omega)
    seg_min rfl) ?_
  refine cut n _ _ 1048827 3 (by omega) (by omega) (conv_data hm n 1048827 3 (by decide) (by decide) (by omega)
    seg_max rfl) ?_
  refine cut n _ _ 1049788 5 (by omega) (by omega) (conv_data hm n 1049788 5 (by decide) (by decide) (by omega)
    seg_key rfl) ?_
  refine cut n _ _ 1050200 4 (by omega) (by omega) (conv_data hm n 1050200 4 (by decide) (by decide) (by omega)
    seg_v12 rfl) ?_
  refine cut n _ _ 1050204 4 (by omega) (by omega) (conv_data hm n 1050204 4 (by decide) (by decide) (by omega)
    seg_v16 rfl) ?_
  refine cut n _ _ 1050280 4 (by omega) (by omega) (conv_data hm n 1050280 4 (by decide) (by decide) (by omega)
    seg_v92 rfl) ?_
  refine cut n _ _ 1050288 4 (by omega) (by omega) (conv_data hm n 1050288 4 (by decide) (by decide) (by omega)
    seg_v100 rfl) ?_
  refine cut n _ _ 1050376 4 (by omega) (by omega) (conv_data hm n 1050376 4 (by decide) (by decide) (by omega)
    seg_v188 rfl) ?_
  refine cut n _ _ 1050868 31 (by omega) (by omega) (conv_data hm n 1050868 31 (by decide) (by decide) (by omega)
    seg_notInit rfl) ?_
  refine cut n _ _ 1051817 1 (by omega) (by omega) (conv_data hm n 1051817 1 (by decide) (by decide) (by omega)
    seg_quote rfl) ?_
  refine cut n _ _ 1051834 1 (by omega) (by omega) (conv_data hm n 1051834 1 (by decide) (by decide) (by omega)
    seg_colon2 rfl) ?_
  refine cut n _ _ 1051836 8 (by omega) (by omega) ((conv_data hm n 1051836 8 (by decide) (by decide) (by omega)
    seg_ts rfl).trans (bytes32_one_word n 1051836 1051836 0)) ?_
  refine cut n _ _ 1055020 4 (by omega) (by omega) (conv_data hm n 1055020 4 (by decide) (by decide) (by omega)
    seg_key116 rfl) ?_
  refine cut n _ _ 1057480 4 (by omega) (by omega) (conv_data hm n 1057480 4 (by decide) (by decide) (by omega)
    seg_vt rfl) ?_
  refine cut n _ _ 1061856 10 (by omega) (by omega) (conv_data hm n 1061856 10 (by decide) (by decide) (by omega)
    seg_esc rfl) ?_
  refine cut n _ _ 1061905 26 (by omega) (by omega) (conv_data hm n 1061905 26 (by decide) (by decide) (by omega)
    seg_lower rfl) ?_
  refine cut n _ _ 1065416 4 (by omega) (by omega) (conv_data hm n 1065416 4 (by decide) (by decide) (by omega)
    seg_157 rfl) ?_
  refine cut n _ _ 1070974 200 (by omega) (by omega) (conv_data hm n 1070974 200 (by decide) (by decide)
    (by omega) seg_lut rfl) ?_
  refine cut n _ _ 1074896 4 (by omega) (by omega) (conv_zero hm n 1074896 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cut n _ _ 1074900 16 (by omega) (by omega) ((memR_zero hm n 1074900 16 (Or.inl (by decide)) (by omega)).trans
    (zero_words n 1074900)) ?_
  refine cut n _ _ 1074920 16 (by omega) (by omega) ((memR_zero hm n 1074920 16 (Or.inl (by decide)) (by omega)).trans
    (zero_words n 1074920)) ?_
  exact true_intro

set_option maxRecDepth 100000 in
/-- **The statics of `storage_balance_bounds`, with the panic path's**: `staticsResP` with the
struct serializer's data (`StorageBalanceBoundsBody.statics306`). -/
theorem staticsRes306P {m : Memory} {L : Nat} (hm : MemImage m L) (n ta len : Nat) (hl1 : len % 65536 = 0)
    (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ tableRes ta ⊢
      stk n 1047840 736 ∗ StorageBalanceBoundsBody.statics306 n ta id 0 0 123 1051836 2048 len ∗
        (PanicStr.panicSlot n ta id ∗ n ↦[wms][ 1050868 ] PanicStr.notInit) := by
  refine (sep_mono_left (memRes306 hm n)).trans ?_
  iintro ⟨⟨STK, RB, LB, CM, CL, KMIN, KMAX, KEY, V12, V16, V92, V100, V188, MSG, Q, CL2, ⟨TS0, TS4⟩, LK, VT, ESC,
    LOW, T157, LUT, HEAD, ⟨B0, B4, B8, B12⟩, ⟨K0, K4, K8, K12⟩, -⟩, HL, #HM, HT⟩
  iunfold tableRes at HT
  icases HT with ⟨T116, T106, T39, T58, T82, T38, T123, T157', T92, T60⟩
  ihave HP : PanicStr.panicSlot (GF := GF) n ta id $$ [V100 T60]
  · iapply PanicStr.panicSlot_of n ta id
    isplitl [V100]
    · iexact V100
    · simp only [id]; iexact T60
  iframe HP MSG
  ihave HEAD := memBytes_addr (a := 1074896) (b := AllocInv.headAddr) rfl $$ HEAD
  ihave Hinv := AllocInv.heapInv_init n 2048 len hl1 hl0 hl2 $$ [HEAD HL]
  · iframe HEAD HL HM
  ihave Hinv := AllocInv.heapInv_mono n 2048 len [] 0 1 (by decide) $$ Hinv
  iunfold StorageBalanceBoundsBody.statics306, SerdeStruct.boundsData
  iunfold FtTotalSupply.statics, FtTotalSupply.vtab, SetupPanicHook.hookCells,
    SetBlockchainInterface.blockchainInterfaceCells, AllocFirstFit.vt, ToVec.tvData, ToString.tsData
  ihave K4 := memBytes_addr (a := 1074920 + 4) (b := 1074924) rfl $$ K4
  ihave K8 := memBytes_addr (a := 1074920 + 8) (b := 1074928) rfl $$ K8
  ihave K12 := memBytes_addr (a := 1074920 + 12) (b := 1074932) rfl $$ K12
  ihave B4 := memBytes_addr (a := 1074900 + 4) (b := 1074904) rfl $$ B4
  ihave B8 := memBytes_addr (a := 1074900 + 8) (b := 1074908) rfl $$ B8
  ihave B12 := memBytes_addr (a := 1074900 + 12) (b := 1074912) rfl $$ B12
  ihave VT := memBytes_addr (a := 1057480) (b := (1057464 : UInt32).toNat + 16) rfl $$ VT
  ihave TS0 := memBytes_addr (a := 1051836) (b := (1051836 : UInt32).toNat) rfl $$ TS0
  ihave TS4 := memBytes_addr (a := 1051836 + 4) (b := (1051836 : UInt32).toNat + 4) rfl $$ TS4
  ihave T157 := memBytes_addr (a := 1065416) (b := (1065404 : UInt32).toNat + 12) rfl $$ T157
  ihave T123 := tablePt_addr (i := 123) (j := (123 : UInt32).toNat) rfl $$ T123
  ihave T157' := tablePt_addr (i := 157) (j := (157 : UInt32).toNat) rfl $$ T157'
  ihave T92 := tablePt_addr (i := 92) (j := (92 : UInt32).toNat) rfl $$ T92
  ihave LOW := memBytes_addr (a := 1061905) (b := 1061808 + 97) rfl $$ LOW
  simp only [id]
  iframe STK K12 K0 K4 K8 LK T116 T106 B0 B4 B8 B12 V16 T39 V92 T58 V188 T82 V12 T38 VT T123 Hinv KEY TS0 TS4
    T157 T157' T92 Q ESC LUT RB LB CM CL KMIN KMAX CL2 LOW

/-- **The statics of `storage_balance_bounds`** (`staticsRes306P`, the panic path's dropped). -/
theorem staticsRes306 {m : Memory} {L : Nat} (hm : MemImage m L) (n ta len : Nat) (hl1 : len % 65536 = 0)
    (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ tableRes ta ⊢
      stk n 1047840 736 ∗ StorageBalanceBoundsBody.statics306 n ta id 0 0 123 1051836 2048 len :=
  (staticsRes306P hm n ta len hl1 hl0 hl2).trans (sep_mono_right sep_elim_left)

end Mem

end WNear.Binary.InitialState
