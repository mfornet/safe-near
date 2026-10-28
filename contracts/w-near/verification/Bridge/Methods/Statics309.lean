import Bridge.Methods.Statics306
import Bridge.Methods.FtMetadataData
import Bridge.Functions.FtMetadataBody

/-!
# What `ft_metadata` (309) starts with: `ft_total_supply`'s statics, the metadata's data, 1024 bytes of stack

`memRes309` carves the instantiated memory into `ft_total_supply`'s cells (`InitialState.memRes0`),
the data the getter (308) and the struct serializer (102) read (`metaData`: `}`, `null`, `{`, `,`,
`:` and the keys at 1048744 .. 1048810, `DEC_DIGITS_LUT` at 1049500, the three constant strings at
1051277, `,` at 1051819, `:` at 1051834, and `ESCAPE` from `' '` to 127 but the digits' entries,
which `ft_total_supply` owns: `escA` at 1061840 and `escB` at 1061866), and 1024 bytes of stack
below 1048576 (309's frame is 160 bytes, 32 more than 306's). `staticsRes309P` gives
`statics309` with the panic path's cells.
-/

namespace WNear.Binary.FtMetadataBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.MetadataFields WNear.Binary.MetadataGetter

/-- `ESCAPE` from `' '` to `'/'` and from `':'` to 127: `escT` around the digits' `esc`. -/
def escA : List UInt8 := escT.take 16
def escB : List UInt8 := escT.drop 26

theorem escT_split : escT = escA ++ SerializeStr.esc ++ escB := by decide

section Data

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The data the metadata's getter and serializer read (owned, returned). -/
def metaData (n : Nat) : IProp GF :=
  iprop(n ↦[wms][ 1048744 ] [125] ∗ n ↦[wms][ 1048754 ] nullStr ∗ n ↦[wms][ 1048758 ] [123] ∗
    n ↦[wms][ 1048759 ] [44] ∗ n ↦[wms][ 1048760 ] [58] ∗ n ↦[wms][ 1048761 ] metaKeys ∗
    n ↦[wms][ 1049500 ] FmtDigits.lut ∗ n ↦[wms][ 1051277 ] metaStrs ∗ n ↦[wms][ 1051819 ] [44] ∗
    n ↦[wms][ 1051834 ] [58] ∗ n ↦[wms][ 1061840 ] escA ∗ n ↦[wms][ 1061866 ] escB)

/-- The statics of `ft_metadata`: `ft_total_supply`'s and `metaData`. -/
noncomputable def statics309 (n ta : Nat) (A : Nat → Nat) (old k3 idx ptr0 : UInt32) (maxP len : Nat) :
    IProp GF :=
  iprop(FtTotalSupply.statics n ta A old k3 idx ptr0 maxP len ∗ metaData n)

end Data

end WNear.Binary.FtMetadataBody

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (dataWord dataWord_eq dataInitK_get)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.MetadataFields WNear.Binary.MetadataGetter WNear.Binary.FtMetadataBody

set_option maxRecDepth 100000 in
theorem seg_escA : seg 1061840 16 = escA := by decide
set_option maxRecDepth 100000 in
theorem seg_escB : seg 1061866 70 = escB := by decide

section Mem

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells) in
open WNear.Binary.SetupPanicHook (hookCells) in
/-- `memRes0` with the metadata's data and 1024 bytes of stack, in address order. -/
theorem memRes309 {m : Memory} {L : Nat} (hm : MemImage m L) (n : Nat) :
    memR (GF := GF) m n 0 L ⊢
      stk n 1047552 1024 ∗ (n ↦[wms][ 1048744 ] [125] ∗ (n ↦[wms][ 1048754 ] nullStr ∗
      (n ↦[wms][ 1048758 ] [123] ∗ (n ↦[wms][ 1048759 ] [44] ∗ (n ↦[wms][ 1048760 ] [58] ∗
      (n ↦[wms][ 1048761 ] metaKeys ∗ (n ↦[wms][ 1049500 ] FmtDigits.lut ∗
      (n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      (n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ (n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗
      (n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ (n ↦[wms][ 1050188 + 100 ] dataWord (1050188 + 100) ∗
      (n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗ (n ↦[wms][ 1050868 ] PanicStr.notInit ∗
      (n ↦[wms][ 1051277 ] metaStrs ∗
      (n ↦[wms][ 1051817 ] [34] ∗ (n ↦[wms][ 1051819 ] [44] ∗ (n ↦[wms][ 1051834 ] [58] ∗
      ((n ↦[i32][ 1051836 ] 1051836 ∗ n ↦[i32][ 1051836 + 4 ] 0) ∗
      (n ↦[i32][ 1055020 ] 116 ∗ (n ↦[i32][ 1057480 ] 123 ∗ (n ↦[wms][ 1061840 ] escA ∗
      (n ↦[wms][ 1061856 ] SerializeStr.esc ∗ (n ↦[wms][ 1061866 ] escB ∗
      (n ↦[i32][ 1065416 ] 157 ∗ (n ↦[wms][ 1070974 ] FmtDigits.lut ∗ (n ↦[i32][ 1074896 ] 0 ∗
      ((n ↦[i32][ 1074900 ] 0 ∗ n ↦[i32][ 1074900 + 4 ] 0 ∗ n ↦[i32][ 1074900 + 8 ] 0 ∗ n ↦[i32][ 1074900 + 12 ] 0) ∗
      ((n ↦[i32][ 1074920 ] 0 ∗ n ↦[i32][ 1074920 + 4 ] 0 ∗ n ↦[i32][ 1074920 + 8 ] 0 ∗
        n ↦[i32][ 1074920 + 12 ] 0) ∗ True))))))))))))))))))))))))))))) := by
  have hL := hm.1
  refine cut n 0 L 1047552 1024 (by omega) (by omega)
    ((memR_zero hm n 1047552 1024 (Or.inr (by decide)) (by omega)).trans (zero_stk n 1047552 1024)) ?_
  refine cut n _ _ 1048744 1 (by omega) (by omega) (conv_data hm n 1048744 1 (by decide) (by decide) (by omega)
    seg_rbrace rfl) ?_
  refine cut n _ _ 1048754 4 (by omega) (by omega) (conv_data hm n 1048754 4 (by decide) (by decide) (by omega)
    seg_null rfl) ?_
  refine cut n _ _ 1048758 1 (by omega) (by omega) (conv_data hm n 1048758 1 (by decide) (by decide) (by omega)
    seg_lbrace rfl) ?_
  refine cut n _ _ 1048759 1 (by omega) (by omega) (conv_data hm n 1048759 1 (by decide) (by decide) (by omega)
    seg_comma rfl) ?_
  refine cut n _ _ 1048760 1 (by omega) (by omega) (conv_data hm n 1048760 1 (by decide) (by decide) (by omega)
    seg_colon rfl) ?_
  refine cut n _ _ 1048761 49 (by omega) (by omega) (conv_data hm n 1048761 49 (by decide) (by decide) (by omega)
    seg_metaKeys rfl) ?_
  refine cut n _ _ 1049500 200 (by omega) (by omega) (conv_data hm n 1049500 200 (by decide) (by decide)
    (by omega) seg_lut2 rfl) ?_
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
  refine cut n _ _ 1051277 40 (by omega) (by omega) (conv_data hm n 1051277 40 (by decide) (by decide) (by omega)
    seg_metaStrs rfl) ?_
  refine cut n _ _ 1051817 1 (by omega) (by omega) (conv_data hm n 1051817 1 (by decide) (by decide) (by omega)
    seg_quote rfl) ?_
  refine cut n _ _ 1051819 1 (by omega) (by omega) (conv_data hm n 1051819 1 (by decide) (by decide) (by omega)
    seg_comma2 rfl) ?_
  refine cut n _ _ 1051834 1 (by omega) (by omega) (conv_data hm n 1051834 1 (by decide) (by decide) (by omega)
    seg_colon2 rfl) ?_
  refine cut n _ _ 1051836 8 (by omega) (by omega) ((conv_data hm n 1051836 8 (by decide) (by decide) (by omega)
    seg_ts rfl).trans (bytes32_one_word n 1051836 1051836 0)) ?_
  refine cut n _ _ 1055020 4 (by omega) (by omega) (conv_data hm n 1055020 4 (by decide) (by decide) (by omega)
    seg_key116 rfl) ?_
  refine cut n _ _ 1057480 4 (by omega) (by omega) (conv_data hm n 1057480 4 (by decide) (by decide) (by omega)
    seg_vt rfl) ?_
  refine cut n _ _ 1061840 16 (by omega) (by omega) (conv_data hm n 1061840 16 (by decide) (by decide) (by omega)
    seg_escA rfl) ?_
  refine cut n _ _ 1061856 10 (by omega) (by omega) (conv_data hm n 1061856 10 (by decide) (by decide) (by omega)
    seg_esc rfl) ?_
  refine cut n _ _ 1061866 70 (by omega) (by omega) (conv_data hm n 1061866 70 (by decide) (by decide) (by omega)
    seg_escB rfl) ?_
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
/-- **The statics of `ft_metadata`, with the panic path's**, and 1024 bytes of stack. -/
theorem staticsRes309P {m : Memory} {L : Nat} (hm : MemImage m L) (n ta len : Nat) (hl1 : len % 65536 = 0)
    (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ tableRes ta ⊢
      stk n 1047552 1024 ∗ statics309 n ta id 0 0 123 1051836 2048 len ∗
        (PanicStr.panicSlot n ta id ∗ n ↦[wms][ 1050868 ] PanicStr.notInit) := by
  refine (sep_mono_left (memRes309 hm n)).trans ?_
  iintro ⟨⟨STK, RB, NUL, LB, CM, CL, KEYS, LUT2, KEY, V12, V16, V92, V100, V188, MSG, STRS, Q, CM2, CL2,
    ⟨TS0, TS4⟩, LK, VT, ESCA, ESC, ESCB, T157, LUT, HEAD, ⟨B0, B4, B8, B12⟩, ⟨K0, K4, K8, K12⟩, -⟩, HL, #HM, HT⟩
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
  iunfold statics309, metaData
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
  simp only [id]
  iframe STK K12 K0 K4 K8 LK T116 T106 B0 B4 B8 B12 V16 T39 V92 T58 V188 T82 V12 T38 VT T123 Hinv KEY TS0 TS4
    T157 T157' T92 Q ESC LUT RB NUL LB CM CL KEYS LUT2 STRS CM2 CL2 ESCA ESCB

end Mem

end WNear.Binary.InitialState
