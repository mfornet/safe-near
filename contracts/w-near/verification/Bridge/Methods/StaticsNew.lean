import Bridge.Methods.StartCells
import Bridge.Methods.NewData
import Bridge.Functions.NewBodyPanic
import Bridge.Functions.StorageRemove

/-!
# What `new` (290) starts with

`memResNew` carves the instantiated memory into the cells `new` owns, in address order: the 736
bytes of stack, the vtable words of the interface's methods `new` calls (`register_len`,
`read_register`, `storage_usage`, `attached_deposit`, `value_return`, `panic_utf8`,
`storage_write`, `storage_read`, `storage_remove`, `storage_has_key`), the two panic messages,
`measure_account_storage_usage`'s `"a"` and `0u128`, the interface's key, the second `"STATE"`,
the allocator's vtable, the heap's head and the hook's and the interface's cells.
`tableResNew`/`tableOfNew`: the table entries `new` reaches.

`staticsResNew`: the statics of the panic paths (`NewBody.staticsNewP`) and those the success
path adds (`staticsNewS`: the `storage_write`, `storage_remove` and `storage_usage` slots, the
allocator's vtable and the empty heap, the first `"STATE"`, `"a"` and `0u128`).
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (dataWord dataWord_eq dataInitK_get)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)

theorem seg_v52 : seg 1050240 4 = dataWord (1050188 + 52) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v64 : seg 1050252 4 = dataWord (1050188 + 64) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v184 : seg 1050372 4 = dataWord (1050188 + 184) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v192 : seg 1050380 4 = dataWord (1050188 + 192) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v196 : seg 1050384 4 = dataWord (1050188 + 196) := by rw [dataWord_eq _ (by decide)]; rfl

section Mem

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The memory's cells `new` owns, in address order. -/
theorem memResNew {m : Memory} {L : Nat} (hm : MemImage m L) (n : Nat) :
    memR (GF := GF) m n 0 L ⊢
      stk n 1047840 736 ∗ (n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      (n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ (n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗
      (n ↦[wms][ 1050188 + 52 ] dataWord (1050188 + 52) ∗ (n ↦[wms][ 1050188 + 64 ] dataWord (1050188 + 64) ∗
      (n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ (n ↦[wms][ 1050188 + 100 ] dataWord (1050188 + 100) ∗
      (n ↦[wms][ 1050188 + 184 ] dataWord (1050188 + 184) ∗ (n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗
      (n ↦[wms][ 1050188 + 192 ] dataWord (1050188 + 192) ∗ (n ↦[wms][ 1050188 + 196 ] dataWord (1050188 + 196) ∗
      (n ↦[wms][ 1050899 ] depositMsg ∗ (n ↦[wms][ 1050932 ] initMsg ∗
      (n ↦[wms][ 1052792 ] [97] ∗ (n ↦[wms][ 1052800 ] List.replicate 16 0 ∗
      (n ↦[i32][ 1055020 ] 116 ∗ (n ↦[wms][ 1056468 ] StateRead.stateKey ∗ (n ↦[i32][ 1057480 ] 123 ∗
      (n ↦[i32][ 1074896 ] 0 ∗
      ((n ↦[i32][ 1074900 ] 0 ∗ n ↦[i32][ 1074900 + 4 ] 0 ∗ n ↦[i32][ 1074900 + 8 ] 0 ∗ n ↦[i32][ 1074900 + 12 ] 0) ∗
      ((n ↦[i32][ 1074920 ] 0 ∗ n ↦[i32][ 1074920 + 4 ] 0 ∗ n ↦[i32][ 1074920 + 8 ] 0 ∗
        n ↦[i32][ 1074920 + 12 ] 0) ∗ True))))))))))))))))))))) := by
  have hL := hm.1
  refine cut n 0 L 1047840 736 (by omega) (by omega)
    ((memR_zero hm n 1047840 736 (Or.inr (by decide)) (by omega)).trans (zero_stk n 1047840 736)) ?_
  refine cut n _ _ 1049788 5 (by omega) (by omega) (conv_data hm n 1049788 5 (by decide) (by decide) (by omega)
    seg_key rfl) ?_
  refine cut n _ _ 1050200 4 (by omega) (by omega) (conv_data hm n 1050200 4 (by decide) (by decide) (by omega)
    seg_v12 rfl) ?_
  refine cut n _ _ 1050204 4 (by omega) (by omega) (conv_data hm n 1050204 4 (by decide) (by decide) (by omega)
    seg_v16 rfl) ?_
  refine cut n _ _ 1050240 4 (by omega) (by omega) (conv_data hm n 1050240 4 (by decide) (by decide) (by omega)
    seg_v52 rfl) ?_
  refine cut n _ _ 1050252 4 (by omega) (by omega) (conv_data hm n 1050252 4 (by decide) (by decide) (by omega)
    seg_v64 rfl) ?_
  refine cut n _ _ 1050280 4 (by omega) (by omega) (conv_data hm n 1050280 4 (by decide) (by decide) (by omega)
    seg_v92 rfl) ?_
  refine cut n _ _ 1050288 4 (by omega) (by omega) (conv_data hm n 1050288 4 (by decide) (by decide) (by omega)
    seg_v100 rfl) ?_
  refine cut n _ _ 1050372 4 (by omega) (by omega) (conv_data hm n 1050372 4 (by decide) (by decide) (by omega)
    seg_v184 rfl) ?_
  refine cut n _ _ 1050376 4 (by omega) (by omega) (conv_data hm n 1050376 4 (by decide) (by decide) (by omega)
    seg_v188 rfl) ?_
  refine cut n _ _ 1050380 4 (by omega) (by omega) (conv_data hm n 1050380 4 (by decide) (by decide) (by omega)
    seg_v192 rfl) ?_
  refine cut n _ _ 1050384 4 (by omega) (by omega) (conv_data hm n 1050384 4 (by decide) (by decide) (by omega)
    seg_v196 rfl) ?_
  refine cut n _ _ 1050899 33 (by omega) (by omega) (conv_data hm n 1050899 33 (by decide) (by decide) (by omega)
    seg_deposit rfl) ?_
  refine cut n _ _ 1050932 41 (by omega) (by omega) (conv_data hm n 1050932 41 (by decide) (by decide) (by omega)
    seg_init rfl) ?_
  refine cut n _ _ 1052792 1 (by omega) (by omega) (conv_data hm n 1052792 1 (by decide) (by decide) (by omega)
    seg_a rfl) ?_
  refine cut n _ _ 1052800 16 (by omega) (by omega) (conv_data hm n 1052800 16 (by decide) (by decide) (by omega)
    seg_zero128 rfl) ?_
  refine cut n _ _ 1055020 4 (by omega) (by omega) (conv_data hm n 1055020 4 (by decide) (by decide) (by omega)
    seg_key116 rfl) ?_
  refine cut n _ _ 1056468 5 (by omega) (by omega) (conv_data hm n 1056468 5 (by decide) (by decide) (by omega)
    seg_key2 rfl) ?_
  refine cut n _ _ 1057480 4 (by omega) (by omega) (conv_data hm n 1057480 4 (by decide) (by decide) (by omega)
    seg_vt rfl) ?_
  refine cut n _ _ 1074896 4 (by omega) (by omega) (conv_zero hm n 1074896 4 (Or.inl (by decide)) (by omega)
    bytes32_zero.symm) ?_
  refine cut n _ _ 1074900 16 (by omega) (by omega) ((memR_zero hm n 1074900 16 (Or.inl (by decide)) (by omega)).trans
    (zero_words n 1074900)) ?_
  refine cut n _ _ 1074920 16 (by omega) (by omega) ((memR_zero hm n 1074920 16 (Or.inl (by decide)) (by omega)).trans
    (zero_words n 1074920)) ?_
  exact true_intro

/-- The table entries `new` reaches through `call_indirect`: the interface's accessor and
initialiser (116, 106), the trampolines of `register_len`, `value_return`, `storage_read`,
`read_register` (39, 58, 82, 38), `attached_deposit`, `storage_has_key`, `panic_utf8` (51, 84,
60), `storage_write`, `storage_remove`, `storage_usage` (81, 83, 48) and wee_alloc's
`min_cell_size` (123). -/
def tableResNew (ta : Nat) : IProp GF :=
  iprop(ta ↦[wt][ 116 ] Ref.func 565 ∗ ta ↦[wt][ 106 ] Ref.func 564 ∗ ta ↦[wt][ 39 ] Ref.func 241 ∗
    ta ↦[wt][ 58 ] Ref.func 260 ∗ ta ↦[wt][ 82 ] Ref.func 284 ∗ ta ↦[wt][ 38 ] Ref.func 240 ∗
    ta ↦[wt][ 51 ] Ref.func 253 ∗ ta ↦[wt][ 84 ] Ref.func 286 ∗ ta ↦[wt][ 60 ] Ref.func 262 ∗
    ta ↦[wt][ 81 ] Ref.func 283 ∗ ta ↦[wt][ 83 ] Ref.func 285 ∗ ta ↦[wt][ 48 ] Ref.func 250 ∗
    ta ↦[wt][ 123 ] Ref.func 578)

set_option maxRecDepth 100000 in
/-- The table entries `new` uses, from the start's table cells. -/
theorem tableOfNew : ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ⊢ tableResNew (GF := GF) 0 := by
  have hs : (([38, 39, 48, 51, 58, 60, 81, 82, 83, 84, 106, 116, 123] : List Nat).map fun i =>
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
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H48, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H51, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H58, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H60, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H81, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H82, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H83, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H84, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H106, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H116, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H123, -⟩
  ihave H38 := e 38 (Ref.func 240) rfl $$ H38
  ihave H39 := e 39 (Ref.func 241) rfl $$ H39
  ihave H48 := e 48 (Ref.func 250) rfl $$ H48
  ihave H51 := e 51 (Ref.func 253) rfl $$ H51
  ihave H58 := e 58 (Ref.func 260) rfl $$ H58
  ihave H60 := e 60 (Ref.func 262) rfl $$ H60
  ihave H81 := e 81 (Ref.func 283) rfl $$ H81
  ihave H82 := e 82 (Ref.func 284) rfl $$ H82
  ihave H83 := e 83 (Ref.func 285) rfl $$ H83
  ihave H84 := e 84 (Ref.func 286) rfl $$ H84
  ihave H106 := e 106 (Ref.func 564) rfl $$ H106
  ihave H116 := e 116 (Ref.func 565) rfl $$ H116
  ihave H123 := e 123 (Ref.func 578) rfl $$ H123
  iunfold tableResNew
  iframe H38 H39 H48 H51 H58 H60 H81 H82 H83 H84 H106 H116 H123

end Mem

end WNear.Binary.InitialState

namespace WNear.Binary.NewBody

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.InitialState
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk)

section Statics

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The statics only `new`'s success path uses: the `storage_write`, `storage_remove` and
`storage_usage` slots, the allocator's vtable and the heap, the key `"STATE"` `state_write`
passes, and `measure_account_storage_usage`'s `"a"` and `0u128`. -/
noncomputable def staticsNewS (n ta : Nat) (A : Nat → Nat) (idx : UInt32) (maxP len : Nat) : IProp GF :=
  iprop(StorageWrite.wslot n ta A ∗ StorageRemove.rslot n ta A ∗ EnvGetters.uslot n ta A ∗
    AllocFirstFit.vt n 1057464 idx ta (A 578) ∗ AllocInv.heapInv n maxP len [] 1 ∗
    n ↦[wms][ 1049788 ] StateRead.stateKey ∗ n ↦[wms][ 1052792 ] [97] ∗
    n ↦[wms][ 1052800 ] List.replicate 16 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The statics of `new`** from the instantiated memory (`MemImage`), its length `len` and
limit 2048, and the table: the 736 bytes of stack below 1048576, the panic paths' statics
(`staticsNewP`, the default hook, the interface not set up) and the success path's
(`staticsNewS`, wee_alloc's vtable index 123, the empty heap). -/
theorem staticsResNew {m : Memory} {L : Nat} (hm : MemImage m L) (n ta len : Nat) (hl1 : len % 65536 = 0)
    (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ tableResNew ta ⊢
      stk n 1047840 736 ∗ staticsNewP n ta id 0 0 ∗ staticsNewS n ta id 123 2048 len := by
  refine (sep_mono_left (memResNew hm n)).trans ?_
  iintro ⟨⟨STK, KEY, V12, V16, V52, V64, V92, V100, V184, V188, V192, V196, MD, MI, MA, MZ, LK, KEY2, VT, HEAD,
    ⟨B0, B4, B8, B12⟩, ⟨K0, K4, K8, K12⟩, -⟩, HL, #HM, HT⟩
  iunfold tableResNew at HT
  icases HT with ⟨T116, T106, T39, T58, T82, T38, T51, T84, T60, T81, T83, T48, T123⟩
  ihave HP : PanicStr.panicSlot (GF := GF) n ta id $$ [V100 T60]
  · iapply PanicStr.panicSlot_of n ta id
    isplitl [V100]
    · iexact V100
    · simp only [id]; iexact T60
  ihave HD : EnvGetters.dslot (GF := GF) n ta id $$ [V64 T51]
  · iapply EnvGetters.dslot_of n ta id
    isplitl [V64]
    · iexact V64
    · simp only [id]; iexact T51
  ihave HU : EnvGetters.uslot (GF := GF) n ta id $$ [V52 T48]
  · iapply EnvGetters.uslot_of n ta id
    isplitl [V52]
    · iexact V52
    · simp only [id]; iexact T48
  ihave HH : StorageHasKey.hslot (GF := GF) n ta id $$ [V196 T84]
  · iapply StorageHasKey.hslot_of n ta id
    isplitl [V196]
    · iexact V196
    · simp only [id]; iexact T84
  ihave HW : StorageWrite.wslot (GF := GF) n ta id $$ [V184 T81]
  · iapply StorageWrite.wslot_of n ta id
    isplitl [V184]
    · iexact V184
    · simp only [id]; iexact T81
  ihave HR : StorageRemove.rslot (GF := GF) n ta id $$ [V192 T83]
  · iapply StorageRemove.rslot_of n ta id
    isplitl [V192]
    · iexact V192
    · simp only [id]; iexact T83
  ihave HEAD := memBytes_addr (a := 1074896) (b := AllocInv.headAddr) rfl $$ HEAD
  ihave Hinv := AllocInv.heapInv_init n 2048 len hl1 hl0 hl2 $$ [HEAD HL]
  · iframe HEAD HL HM
  ihave Hinv := AllocInv.heapInv_mono n 2048 len [] 0 1 (by decide) $$ Hinv
  iunfold staticsNewP, staticsNewS, FtTotalSupply.vtab, SetupPanicHook.hookCells,
    SetBlockchainInterface.blockchainInterfaceCells, AllocFirstFit.vt
  ihave K4 := memBytes_addr (a := 1074920 + 4) (b := 1074924) rfl $$ K4
  ihave K8 := memBytes_addr (a := 1074920 + 8) (b := 1074928) rfl $$ K8
  ihave K12 := memBytes_addr (a := 1074920 + 12) (b := 1074932) rfl $$ K12
  ihave B4 := memBytes_addr (a := 1074900 + 4) (b := 1074904) rfl $$ B4
  ihave B8 := memBytes_addr (a := 1074900 + 8) (b := 1074908) rfl $$ B8
  ihave B12 := memBytes_addr (a := 1074900 + 12) (b := 1074912) rfl $$ B12
  ihave VT := memBytes_addr (a := 1057480) (b := (1057464 : UInt32).toNat + 16) rfl $$ VT
  ihave T123 := tablePt_addr (i := 123) (j := (123 : UInt32).toNat) rfl $$ T123
  simp only [id]
  iframe STK K12 K0 K4 K8 LK T116 T106 B0 B4 B8 B12 V16 T39 V92 T58 V188 T82 V12 T38 HD HH HP MD MI KEY2
    HW HR HU VT T123 Hinv KEY MA MZ

end Statics

end WNear.Binary.NewBody
