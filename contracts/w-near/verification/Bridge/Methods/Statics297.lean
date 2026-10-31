import Bridge.Methods.Code297

/-! Linear entry resources of the copied-array absent-account balance path.
The frame and static data are carved from the instantiated memory image; table
entries are selected once from the instantiated table. -/
namespace WNear.Binary.InitialState
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
section
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
/-- The initial table entries for the copied-array balance body, extracted once. -/
theorem table297Of : ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ⊢ tableRes (GF := GF) 0 ∗ 0 ↦[wt][ 44 ] Ref.func 246 := by
  have hs : (([38, 39, 44, 58, 60, 82, 92, 106, 116, 123, 157] : List Nat).map fun i =>
      ((Loc.tableElem 0 i, .ref wTable.elems[i]!) : Loc × Cell NearState)).Sublist tabCells :=
    List.Sublist.map _ (by decide)
  refine (bigSepL_sublist (Φ := fun p : Loc × Cell NearState => iprop(p.1 ↦ₛ p.2)) hs).trans ?_
  simp only [List.map_cons, List.map_nil]
  have e : ∀ i (r : Ref), wTable.elems[i]! = r →
      ((Loc.tableElem 0 i ↦ₛ (.ref wTable.elems[i]! : Cell NearState)) : IProp GF) ⊢ 0 ↦[wt][ i ] r := by
    intro i r hr; rw [hr]; exact .rfl
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H38, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H39, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H44, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H58, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H60, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H82, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H92, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H106, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H116, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H123, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H157, -⟩
  ihave H38 := e 38 (Ref.func 240) rfl $$ H38
  ihave H39 := e 39 (Ref.func 241) rfl $$ H39
  ihave H44 := e 44 (Ref.func 246) rfl $$ H44
  ihave H58 := e 58 (Ref.func 260) rfl $$ H58
  ihave H60 := e 60 (Ref.func 262) rfl $$ H60
  ihave H82 := e 82 (Ref.func 284) rfl $$ H82
  ihave H92 := e 92 (Ref.func 353) rfl $$ H92
  ihave H106 := e 106 (Ref.func 564) rfl $$ H106
  ihave H116 := e 116 (Ref.func 565) rfl $$ H116
  ihave H123 := e 123 (Ref.func 578) rfl $$ H123
  ihave H157 := e 157 (Ref.func 759) rfl $$ H157
  isplitl [H38 H39 H58 H82 H92 H106 H116 H123 H157 H60]
  · iunfold tableRes
    iframe H38 H39 H58 H82 H92 H106 H116 H123 H157 H60
  · iexact H44


open WNear.Binary.Interface (dataWord dataWord_eq)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)
theorem seg_v36 : seg 1050224 4 = dataWord (1050188 + 36) := by rw [dataWord_eq _ (by decide)]; rfl

open WNear.Binary.BalanceOf297AbsentCall
open WNear.Binary.FtTotalSupply (statics)

/-- The exact initial frame cells for the function-297 body, in address order. -/
def frame297 (n : Nat) : IProp GF :=
  iprop(stk n 1047824 592 ∗
    n ↦[wms][ 1048416 ] List.replicate 8 0 ∗
    n ↦[wms][ 1048424 ] List.replicate 16 0 ∗
    n ↦[wms][ 1048440 ] List.replicate 8 0 ∗
    n ↦[wms][ 1048448 ] List.replicate 8 0 ∗
    n ↦[i32][ 1048456 ] 0 ∗
    n ↦[wms][ 1048464 ] List.replicate 12 0 ∗
    n ↦[wms][ 1048476 ] List.replicate 28 0 ∗
    n ↦[wms][ 1048504 ] List.replicate 12 0 ∗
    n ↦[wms][ 1048516 ] List.replicate 4 0 ∗
    n ↦[wms][ 1048520 ] List.replicate 24 0 ∗
    n ↦[wms][ 1048544 ] List.replicate 8 0 ∗
    n ↦[i32][ 1048552 ] 0 ∗
    n ↦[wms][ 1048556 ] List.replicate 4 0 ∗
    n ↦[wms][ 1048560 ] List.replicate 12 0 ∗
    True)

theorem frame297_of {m : Memory} {L : Nat} (hm : MemImage m L) (n : Nat) :
    memR (GF := GF) m n 1047824 752 ⊢ frame297 n := by
  unfold frame297
  have hL := hm.1
  refine cut n 1047824 752 1047824 592 (by omega) (by omega)
    ((memR_zero hm n 1047824 592 (Or.inr (by decide)) (by omega)).trans (zero_stk n 1047824 592)) ?_
  refine cut n _ _ 1048416 8 (by omega) (by omega) (conv_zero hm n 1048416 8 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048424 16 (by omega) (by omega) (conv_zero hm n 1048424 16 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048440 8 (by omega) (by omega) (conv_zero hm n 1048440 8 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048448 8 (by omega) (by omega) (conv_zero hm n 1048448 8 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048456 4 (by omega) (by omega) (conv_zero hm n 1048456 4 (Or.inr (by decide)) (by omega) bytes32_zero.symm) ?_
  refine cut n _ _ 1048464 12 (by omega) (by omega) (conv_zero hm n 1048464 12 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048476 28 (by omega) (by omega) (conv_zero hm n 1048476 28 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048504 12 (by omega) (by omega) (conv_zero hm n 1048504 12 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048516 4 (by omega) (by omega) (conv_zero hm n 1048516 4 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048520 24 (by omega) (by omega) (conv_zero hm n 1048520 24 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048544 8 (by omega) (by omega) (conv_zero hm n 1048544 8 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048552 4 (by omega) (by omega) (conv_zero hm n 1048552 4 (Or.inr (by decide)) (by omega) bytes32_zero.symm) ?_
  refine cut n _ _ 1048556 4 (by omega) (by omega) (conv_zero hm n 1048556 4 (Or.inr (by decide)) (by omega) rfl) ?_
  refine cut n _ _ 1048560 12 (by omega) (by omega) (conv_zero hm n 1048560 12 (Or.inr (by decide)) (by omega) rfl) ?_
  exact true_intro

theorem memRes297 {m : Memory} {L : Nat} (hm : MemImage m L) (n : Nat) :
    memR (GF := GF) m n 0 L ⊢
      frame297 n ∗ (n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      (n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ (n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗
      n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗
      (n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ (n ↦[wms][ 1050188 + 100 ] dataWord (1050188 + 100) ∗
      (n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗ (n ↦[wms][ 1050868 ] PanicStr.notInit ∗
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

theorem statics297P {m : Memory} {L : Nat} (hm : MemImage m L) (n ta len : Nat) (hl1 : len % 65536 = 0)
    (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ (tableRes ta ∗ ta ↦[wt][ 44 ] Ref.func 246) ⊢
      frame297 n ∗ FtTotalSupply.statics n ta id 0 0 123 1051836 2048 len ∗
        (PanicStr.panicSlot n ta id ∗ n ↦[wms][ 1050868 ] PanicStr.notInit) ∗
        n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ ta ↦[wt][ 44 ] Ref.func 246 ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable := by
  refine (sep_mono_left (memRes297 hm n)).trans ?_
  iintro ⟨⟨STK, KEY, V12, V16, V36, V92, V100, V188, MSG, Q, ⟨TS0, TS4⟩, LK, VT, ESC, PESC, HEX, T157, LUT, WIDTH, HEAD,
    ⟨B0, B4, B8, B12⟩, ⟨K0, K4, K8, K12⟩, -⟩, HL, #HM, ⟨HT, T44⟩⟩
  iunfold tableRes at HT
  icases HT with ⟨T116, T106, T39, T58, T82, T38, T123, T157', T92, T60⟩
  ihave HP : PanicStr.panicSlot (GF := GF) n ta id $$ [V100 T60]
  · iapply PanicStr.panicSlot_of n ta id
    isplitl [V100]
    · iexact V100
    · simp only [id]; iexact T60
  iframe HP MSG V36 T44 PESC WIDTH HEX
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


theorem startRes297_gen {m : Memory} {L : Nat} (hm : MemImage m L) (cfg : RuntimeConfig) (h : NearState) :
    ((Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗ memR m 0 0 L : IProp GF)
    ⊢ |==> (code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ frame297 0 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗
        (PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] PanicStr.notInit) ∗
        0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable) := by
  iintro ⟨⟨Hi, Hm, HL, Hg, Hh, Hgas⟩, HT, HF, HM⟩
  imod pointsTo_persist _ _ $$ Hi with #Hi
  imod pointsTo_persist _ _ $$ Hm with #Hm
  imod persistList _ $$ HF with #HF
  ihave HT := table297Of $$ HT
  ihave HS := statics297P hm 0 0 memLen (by decide) (by decide) (by decide) $$ [HM HL HT]
  · iframe HM HL HT
    iunfold memLimit
    iexact Hm
  ihave #Hk := code297_of cfg h $$ []
  · iframe HF
    isplitl []
    · iunfold instPt; iexact Hi
    · iunfold memLimit; iexact Hm
  imodintro
  iframe Hk Hg Hh Hgas HS
  iunfold instPt
  iexact Hi

theorem startRes297 (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢
      |==> (code297 cfg.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ 0 ↪[inst] wInst ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗
        gasPt h.gas h.gasProfile h.actionProfile ∗ frame297 0 ∗
        statics 0 0 id 0 0 123 1051836 2048 memLen ∗
        (PanicStr.panicSlot 0 0 id ∗ 0 ↦[wms][ 1050868 ] PanicStr.notInit) ∗
        0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable) :=
  (startCells cfg h).trans ((startSplit cfg h).trans (startRes297_gen wDataMem_image cfg h))

end
end WNear.Binary.InitialState
