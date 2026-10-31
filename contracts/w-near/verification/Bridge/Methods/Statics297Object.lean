import Bridge.Methods.Statics297
import Bridge.Functions.SerdeObjectNoEsc

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.InitialState
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open WNear.Binary.Interface (dataWord dataWord_eq)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.BalanceOf297AbsentCall
open WNear.Binary.FtTotalSupply (statics)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000

theorem seg_ident : seg 1048576 10 = SerdeIdent.identBytes := by decide +kernel

theorem memRes297Obj {m : Memory} {L : Nat} (hm : MemImage m L) (n : Nat) :
    memR (GF := GF) m n 0 L ⊢
      frame297 n ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗ (n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      (n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ (n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗
      n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗
      (n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ (n ↦[wms][ 1050188 + 100 ] dataWord (1050188 + 100) ∗
      (n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗ (n ↦[wms][ 1050868 ] PanicStr.notInit ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
      (n ↦[wms][ 1051817 ] [34] ∗ ((n ↦[i32][ 1051836 ] 1051836 ∗ n ↦[i32][ 1051836 + 4 ] 0) ∗
      (n ↦[i32][ 1055020 ] 116 ∗ (n ↦[i32][ 1057480 ] 123 ∗ (n ↦[wms][ 1061856 ] SerializeStr.esc ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      (n ↦[i32][ 1065416 ] 157 ∗ (n ↦[wms][ 1070974 ] FmtDigits.lut ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ (n ↦[i32][ 1074896 ] 0 ∗
      ((n ↦[i32][ 1074900 ] 0 ∗ n ↦[i32][ 1074900 + 4 ] 0 ∗ n ↦[i32][ 1074900 + 8 ] 0 ∗ n ↦[i32][ 1074900 + 12 ] 0) ∗
      ((n ↦[i32][ 1074920 ] 0 ∗ n ↦[i32][ 1074920 + 4 ] 0 ∗ n ↦[i32][ 1074920 + 8 ] 0 ∗
        n ↦[i32][ 1074920 + 12 ] 0) ∗ True))))))))))))))))) := by
  have hL := hm.1
  refine cut n 0 L 1047824 752 (by omega) (by omega)
    (frame297_of hm n) ?_
  refine cut n _ _ 1048576 10 (by omega) (by omega)
    (conv_data hm n 1048576 10 (by decide) (by decide) (by omega) seg_ident rfl) ?_
  refine cut n _ _ 1049788 5 (by omega) (by omega) (conv_data hm n 1049788 5 (by decide) (by decide) (by omega)
    seg_key rfl) ?_
  refine cut n _ _ 1050200 4 (by omega) (by omega) (conv_data hm n 1050200 4 (by decide) (by decide) (by omega)
    seg_v12 rfl) ?_
  refine cut n _ _ 1050204 4 (by omega) (by omega) (conv_data hm n 1050204 4 (by decide) (by decide) (by omega)
    seg_v16 rfl) ?_
  refine cut n _ _ 1050224 4 (by omega) (by omega) (conv_data hm n 1050224 4 (by decide) (by decide) (by omega)
    seg_v36 rfl) ?_
  refine cut n _ _ 1050280 4 (by omega) (by omega) (conv_data hm n 1050280 4 (by decide) (by decide) (by omega)
    seg_v92 rfl) ?_
  refine cut n _ _ 1050288 4 (by omega) (by omega) (conv_data hm n 1050288 4 (by decide) (by decide) (by omega)
    seg_v100 rfl) ?_
  refine cut n _ _ 1050376 4 (by omega) (by omega) (conv_data hm n 1050376 4 (by decide) (by decide) (by omega)
    seg_v188 rfl) ?_
  refine cut n _ _ 1050868 31 (by omega) (by omega) (conv_data hm n 1050868 31 (by decide) (by decide) (by omega)
    seg_notInit rfl) ?_
  refine cut n _ _ 1051092 10 (by omega) (by omega)
    (conv_data hm n 1051092 10 (by decide) (by decide) (by omega) SerdeKey.keyData_segment rfl) ?_
  refine cut n _ _ 1051817 1 (by omega) (by omega) (conv_data hm n 1051817 1 (by decide) (by decide) (by omega)
    seg_quote rfl) ?_
  refine cut n _ _ 1051836 8 (by omega) (by omega) ((conv_data hm n 1051836 8 (by decide) (by decide) (by omega)
    seg_ts rfl).trans (bytes32_one_word n 1051836 1051836 0)) ?_
  refine cut n _ _ 1055020 4 (by omega) (by omega) (conv_data hm n 1055020 4 (by decide) (by decide) (by omega)
    seg_key116 rfl) ?_
  refine cut n _ _ 1057480 4 (by omega) (by omega) (conv_data hm n 1057480 4 (by decide) (by decide) (by omega)
    seg_vt rfl) ?_
  refine cut n _ _ 1061856 10 (by omega) (by omega) (conv_data hm n 1061856 10 (by decide) (by decide) (by omega)
    seg_esc rfl) ?_
  refine cut n _ _ 1062392 256 (by omega) (by omega) (conv_data hm n 1062392 256 (by decide) (by decide) (by omega)
    ParseStr.escData_segment rfl) ?_
  refine cut n _ _ 1062712 256 (by omega) (by omega) (conv_data hm n 1062712 256 (by decide) (by decide) (by omega)
    SerdeEsc.hexData_segment rfl) ?_
  refine cut n _ _ 1065416 4 (by omega) (by omega) (conv_data hm n 1065416 4 (by decide) (by decide) (by omega)
    seg_157 rfl) ?_
  refine cut n _ _ 1070974 200 (by omega) (by omega) (conv_data hm n 1070974 200 (by decide) (by decide)
    (by omega) seg_lut rfl) ?_
  refine cut n _ _ 1071704 256 (by omega) (by omega) (conv_data hm n 1071704 256 (by decide) (by decide) (by omega)
    FromUtf8Gen.widthData_segment rfl) ?_
  refine cut n _ _ 1074896 4 (by omega) (by omega) (conv_zero hm n 1074896 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cut n _ _ 1074900 16 (by omega) (by omega) ((memR_zero hm n 1074900 16 (Or.inl (by decide)) (by omega)).trans
    (zero_words n 1074900)) ?_
  refine cut n _ _ 1074920 16 (by omega) (by omega) ((memR_zero hm n 1074920 16 (Or.inl (by decide)) (by omega)).trans
    (zero_words n 1074920)) ?_
  exact true_intro

set_option maxHeartbeats 32000000 in
/-- The actual instantiated function cells supply the shallow ignored-reader code. -/
theorem ignored_code_of (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ□ p.2) ∗ (0 ↪[inst] wInst : IProp GF) ⊢
      SerdeIgnValue.code81 0 wInst id := by
  iintro ⟨#HF, #Hi⟩
  simp only [SerdeIgnValue.code81, SerdeIgnNum.numCode, VecAppend.appCode, id]
  repeat' (first
    | iexact Hi
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | isplitl [])

theorem statics297PObj {m : Memory} {L : Nat} (hm : MemImage m L) (n ta len : Nat) (hl1 : len % 65536 = 0)
    (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ (tableRes ta ∗ ta ↦[wt][ 44 ] Ref.func 246) ⊢
      frame297 n ∗ FtTotalSupply.statics n ta id 0 0 123 1051836 2048 len ∗
        (PanicStr.panicSlot n ta id ∗ n ↦[wms][ 1050868 ] PanicStr.notInit) ∗
        n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ ta ↦[wt][ 44 ] Ref.func 246 ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes := by
  refine (sep_mono_left (memRes297Obj hm n)).trans ?_
  iintro ⟨⟨STK, IDENT, KEY, V12, V16, V36, V92, V100, V188, MSG, KEYNAME, Q, ⟨TS0, TS4⟩, LK, VT, ESC, PESC, HEX, T157, LUT, WIDTH, HEAD,
    ⟨B0, B4, B8, B12⟩, ⟨K0, K4, K8, K12⟩, -⟩, HL, #HM, ⟨HT, T44⟩⟩
  iunfold tableRes at HT
  icases HT with ⟨T116, T106, T39, T58, T82, T38, T123, T157', T92, T60⟩
  ihave HP : PanicStr.panicSlot (GF := GF) n ta id $$ [V100 T60]
  · iapply PanicStr.panicSlot_of n ta id
    isplitl [V100]
    · iexact V100
    · simp only [id]; iexact T60
  iframe HP MSG V36 T44 PESC WIDTH HEX IDENT KEYNAME
  ihave HEAD := memBytes_addr (a := 1074896) (b := AllocInv.headAddr) rfl $$ HEAD
  ihave Hinv := AllocInv.heapInv_init n 2048 len hl1 hl0 hl2 $$ [HEAD HL]
  · iframe HEAD HL HM
  ihave Hinv := AllocInv.heapInv_mono n 2048 len [] 0 1 (by decide) $$ Hinv
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
    T157 T157' T92 Q ESC LUT


theorem startRes297Obj_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ SerdeIgnValue.code81 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ frame297 0 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗
        (PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] PanicStr.notInit) ∗
        0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ 0 ↦[wms][ 1048576 ] SerdeIdent.identBytes) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := table297Of $$ HT
  ihave HS := statics297PObj hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  ihave #Hk := code297_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  ihave #HIgn := ignored_code_of cfg h $$ [HF]
  · iframe HF
    iunfold instPt
    iexact Hi
  imodintro
  iframe HIgn Hk Hg Hh Hgas HS
  iunfold instPt
  iexact Hi

theorem startRes297Obj (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
      |==> (code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ SerdeIgnValue.code81 0 wInst id ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ frame297 0 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗
        (PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] PanicStr.notInit) ∗
        0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
        0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ 0 ↦[wms][ 1048576 ] SerdeIdent.identBytes) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startRes297Obj_gen wDataMem_image cfg h))

end WNear.Binary.InitialState
