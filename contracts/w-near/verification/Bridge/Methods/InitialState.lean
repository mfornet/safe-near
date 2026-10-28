import Bridge.Functions.FtTotalSupply
import Bridge.Functions.PanicStr
import NearLogic.Instantiate

/-!
# What a method of `contract.wasm` starts with

The bridge from the instantiated store `wStore` (`Binary/Instance.lean`) to the resources the
specifications own. `wDataMem` (the memory: the data segment written at 1048576 into 1024 empty
pages) is never evaluated: `wDataMem_facts` reads it through `writeBytes_spec`, as the data
segment `dataInitK` and zeros elsewhere.

* `memRes0`: a memory with the instantiated image (`MemImage`; `wDataMem_image`), owned as one byte
  list (`memR`), carved (in term mode: the proof mode would try to evaluate the byte list) into the
  cells `ft_total_supply` owns: the 736 bytes of stack below 1048576, `"STATE"`, the interface's
  vtable words, `to_string`'s data, the `LocalKey` word, the allocator's policy vtable word, the
  quote, `ESCAPE` and digit tables, and the zeroed statics after the data segment (the heap head,
  `BLOCKCHAIN_INTERFACE`, the panic hook); and for the panic path (`PanicStr`), the vtable word of
  `panic_utf8` and `PanicOnDefault`'s message.
* `tableRes`: the table entries `ft_total_supply` uses, and the `panic_utf8` trampoline's.
* `staticsResP`: `FtTotalSupply.statics` from the memory, the table, the memory length and limit
  (`heapInv_init`), with the panic path's cells (`panicSlot`, the message); `staticsRes` drops
  them.

The cells of the store themselves (`startCells`) are taken in `StartCells.lean`.
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (dataWord dataWord_eq dataInitK_get)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocNewCell (memBytes_addr)

/-! ## The memory after instantiation -/

theorem dataInitK_size : dataInitK.size = 26319 := by simp [dataInitK, ByteArray.size]

/-- The memory's length after instantiation: 1024 pages. -/
def memLen : Nat := 1024 * 65536

theorem byteArray_get (b : ByteArray) (i : Nat) : b[i]! = b.data[i]! := by
  by_cases h : i < b.size
  · rw [getElem!_pos b i h, getElem!_pos b.data i h]; rfl
  · rw [getElem!_neg b i h, getElem!_neg b.data i h]

theorem wDataMem_facts : wDataMem.wf ∧ wDataMem.byteSize = memLen ∧ wDataMem.max = some 2048 ∧
    ∀ j, wDataMem.read8 j =
      if 1048576 ≤ j ∧ j < 1048576 + 26319 then wNearSource.read (159306 + (j - 1048576)) else 0 := by
  obtain ⟨m', hw, hwf, hsz, hmx, hrd⟩ := writeBytes_spec (Memory.new_wf 1024 (some 2048)) (addr := 1048576)
    (bytes := dataInitK) (by rw [dataInitK_size, Memory.new_byteSize]; simp [pageSize])
  have hd : wDataMem = m' := by unfold wDataMem; rw [hw]; rfl
  rw [hd]
  refine ⟨hwf, by rw [hsz, Memory.new_byteSize]; rfl, by rw [hmx]; rfl, fun j => ?_⟩
  rw [hrd, dataInitK_size, Memory.new_read8]
  split
  · rw [byteArray_get, dataInitK_get _ (by omega)]
  · rfl

theorem readList_eq (m : Memory) (a len : Nat) :
    m.readList a len = (List.range len).map fun i => m.read8 (a + i) := by
  unfold Memory.readList; rfl

theorem readList_add (m : Memory) (a k l : Nat) :
    m.readList a (k + l) = m.readList a k ++ m.readList (a + k) l := by
  simp only [readList_eq, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Nat.add_assoc]

/-- Outside the data segment, zeros. -/
theorem readList_zero (a len : Nat) (h : 1048576 + 26319 ≤ a ∨ a + len ≤ 1048576) :
    wDataMem.readList a len = List.replicate len 0 := by
  rw [readList_eq]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_map, List.getElem_range, List.getElem_replicate, wDataMem_facts.2.2.2]
  rw [if_neg (by simp at h1; omega)]

/-- Inside, the binary's bytes. -/
theorem readList_data (a len : Nat) (h1 : 1048576 ≤ a) (h2 : a + len ≤ 1048576 + 26319) :
    wDataMem.readList a len = (List.range len).map fun k => wNearSource.read (159306 + (a - 1048576) + k) := by
  rw [readList_eq]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [wDataMem_facts.2.2.2, if_pos (by omega), show 159306 + (a + i - 1048576) = 159306 + (a - 1048576) + i by omega]

/-! ## The data segment's bytes the specifications own -/

/-- The data segment's `len` bytes from `a`. -/
noncomputable def seg (a len : Nat) : List UInt8 :=
  (List.range len).map fun k => wNearSource.read (159306 + (a - 1048576) + k)

theorem seg_v12 : seg 1050200 4 = dataWord (1050188 + 12) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v16 : seg 1050204 4 = dataWord (1050188 + 16) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v92 : seg 1050280 4 = dataWord (1050188 + 92) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v100 : seg 1050288 4 = dataWord (1050188 + 100) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_v188 : seg 1050376 4 = dataWord (1050188 + 188) := by rw [dataWord_eq _ (by decide)]; rfl
theorem seg_key : seg 1049788 5 = StateRead.stateKey := StateRead.stateKey_data
/-- `PanicOnDefault`'s message. -/
theorem seg_notInit : seg 1050868 31 = PanicStr.notInit := PanicStr.notInit_data
theorem seg_quote : seg 1051817 1 = [34] := by decide
/-- `to_string`'s `fmt::Arguments` pieces pointer and count. -/
theorem seg_ts : seg 1051836 8 = bytes32 1051836 ++ bytes32 0 := by decide
/-- The `LocalKey` of `BLOCKCHAIN_INTERFACE`: its accessor's table index 116. -/
theorem seg_key116 : seg 1055020 4 = bytes32 116 := by decide
/-- wee_alloc's policy vtable: `min_cell_size` at table index 123. -/
theorem seg_vt : seg 1057480 4 = bytes32 123 := by decide
theorem seg_esc : seg 1061856 10 = SerializeStr.esc := by decide
/-- `u128`'s `Display` vtable slot: table index 157. -/
theorem seg_157 : seg 1065416 4 = bytes32 157 := by decide
theorem seg_lut : seg 1070974 200 = FmtDigits.lut := FmtDigits.lut_data

/-- What the specifications need of the instantiated memory: its first `L` bytes are the data
segment at 1048576 and zeros elsewhere. Stated for any memory, so that the proof never sees the
concrete one (whose byte list the proof mode would try to evaluate). -/
def MemImage (m : Memory) (L : Nat) : Prop :=
  1074936 ≤ L ∧ ∀ j, j < L →
    m.read8 j = if 1048576 ≤ j ∧ j < 1048576 + 26319 then wNearSource.read (159306 + (j - 1048576)) else 0

theorem wDataMem_image : MemImage wDataMem memLen :=
  ⟨by decide, fun j _ => wDataMem_facts.2.2.2 j⟩

theorem image_zero {m : Memory} {L : Nat} (hm : MemImage m L) (a len : Nat)
    (h : 1048576 + 26319 ≤ a ∨ a + len ≤ 1048576) (hb : a + len ≤ L) :
    m.readList a len = List.replicate len 0 := by
  rw [readList_eq]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, List.getElem_replicate, hm.2 _ (by omega)]
  rw [if_neg (by omega)]

theorem image_data {m : Memory} {L : Nat} (hm : MemImage m L) (a len : Nat) (h1 : 1048576 ≤ a)
    (h2 : a + len ≤ 1048576 + 26319) (hb : a + len ≤ L) : m.readList a len = seg a len := by
  rw [readList_eq, seg]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  rw [hm.2 _ (by omega), if_pos (by omega), show 159306 + (a + i - 1048576) = 159306 + (a - 1048576) + i by omega]

section Mem

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The bytes of the memory `m` from `a`. -/
def memR (m : Memory) (n a len : Nat) : IProp GF := n ↦[wms][ a ] m.readList a len

theorem carve (m : Memory) (n a L k b M : Nat) (hb : b = a + k) (hM : M = L - k) (h : k ≤ L) :
    memR (GF := GF) m n a L ⊢ memR m n a k ∗ memR m n b M := by
  subst hb hM
  have e := readList_add m a k (L - k)
  rw [Nat.add_sub_cancel' h] at e
  have e2 := memBytes_append (GF := GF) (H := NearState) n a (m.readList a k) (m.readList (a + k) (L - k))
  rw [Memory.readList_length] at e2
  unfold memR
  rw [e]
  exact e2.1

theorem memR_zero {m : Memory} {L : Nat} (hm : MemImage m L) (n a len : Nat)
    (h : 1048576 + 26319 ≤ a ∨ a + len ≤ 1048576) (hb : a + len ≤ L) :
    memR (GF := GF) m n a len ⊢ n ↦[wms][ a ] List.replicate len 0 := by
  unfold memR; rw [image_zero hm a len h hb]

theorem memR_data {m : Memory} {L : Nat} (hm : MemImage m L) (n a len : Nat) (h1 : 1048576 ≤ a)
    (h2 : a + len ≤ 1048576 + 26319) (hb : a + len ≤ L) :
    memR (GF := GF) m n a len ⊢ n ↦[wms][ a ] seg a len := by
  unfold memR; rw [image_data hm a len h1 h2 hb]

theorem zero_stk (n a len : Nat) : n ↦[wms][ a ] List.replicate len (0 : UInt8) ⊢ stk (GF := GF) n a len := by
  iintro H; iunfold stk; iexists List.replicate len 0; iframe H; ipureintro; simp

theorem bytes32_zero : bytes32 0 = List.replicate 4 (0 : UInt8) := by decide

theorem zero_words (n a : Nat) :
    n ↦[wms][ a ] List.replicate 16 (0 : UInt8) ⊢ (n ↦[i32][ a ] 0 ∗ n ↦[i32][ a + 4 ] 0 ∗
      n ↦[i32][ a + 8 ] 0 ∗ n ↦[i32][ a + 12 ] 0 : IProp GF) := by
  rw [show List.replicate 16 (0 : UInt8) = bytes32 0 ++ (bytes32 0 ++ (bytes32 0 ++ bytes32 0)) by decide]
  iintro H
  icases BorshFT.splitB (a := a) (b := a + 4) _ _ (by simp) $$ H with ⟨H0, H⟩
  icases BorshFT.splitB (a := a + 4) (b := a + 8) _ _ (by simp) $$ H with ⟨H4, H⟩
  icases BorshFT.splitB (a := a + 8) (b := a + 12) _ _ (by simp) $$ H with ⟨H8, H12⟩
  iframe H0 H4 H8 H12

/-- Cut the piece `[a, a + len)` out of `[c, c + R)`, dropping what lies before it. -/
theorem cut {m : Memory} (n c R a len : Nat) {P Q : IProp GF} (hc : c ≤ a) (hR : a + len ≤ c + R)
    (hP : memR m n a len ⊢ P) (hQ : memR m n (a + len) (c + R - (a + len)) ⊢ Q) :
    memR m n c R ⊢ P ∗ Q :=
  (carve m n c R (a - c) a (R - (a - c)) (by omega) rfl (by omega)).trans <|
    sep_elim_right.trans <|
      (carve m n a (R - (a - c)) len (a + len) (c + R - (a + len)) rfl (by omega) (by omega)).trans
        (sep_mono hP hQ)

theorem conv_zero {m : Memory} {L : Nat} (hm : MemImage m L) (n a len : Nat)
    (h : 1048576 + 26319 ≤ a ∨ a + len ≤ 1048576) (hb : a + len ≤ L) {bs : List UInt8}
    (hbs : List.replicate len 0 = bs) : memR (GF := GF) m n a len ⊢ n ↦[wms][ a ] bs :=
  (memR_zero hm n a len h hb).trans (AllocNewCell.memBytes_eq hbs)

theorem conv_data {m : Memory} {L : Nat} (hm : MemImage m L) (n a len : Nat) (h1 : 1048576 ≤ a)
    (h2 : a + len ≤ 1048576 + 26319) (hb : a + len ≤ L) {b : Nat} {bs : List UInt8} (hbs : seg a len = bs)
    (hab : a = b) : memR (GF := GF) m n a len ⊢ n ↦[wms][ b ] bs :=
  (memR_data hm n a len h1 h2 hb).trans ((AllocNewCell.memBytes_eq hbs).trans (memBytes_addr hab))

theorem bytes32_one_word (n a : Nat) (x y : UInt32) :
    (n ↦[wms][ a ] (bytes32 x ++ bytes32 y) : IProp GF) ⊢ n ↦[i32][ a ] x ∗ n ↦[i32][ a + 4 ] y :=
  BorshFT.split64' x y rfl

open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells) in
open WNear.Binary.SetupPanicHook (hookCells) in
/-- The memory's cells, in address order (term-mode carving: the proof mode is not used on
the memory's byte list). -/
theorem memRes0 {m : Memory} {L : Nat} (hm : MemImage m L) (n : Nat) :
    memR (GF := GF) m n 0 L ⊢
      stk n 1047840 736 ∗ (n ↦[wms][ 1049788 ] StateRead.stateKey ∗
      (n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ (n ↦[wms][ 1050188 + 16 ] dataWord (1050188 + 16) ∗
      (n ↦[wms][ 1050188 + 92 ] dataWord (1050188 + 92) ∗ (n ↦[wms][ 1050188 + 100 ] dataWord (1050188 + 100) ∗
      (n ↦[wms][ 1050188 + 188 ] dataWord (1050188 + 188) ∗ (n ↦[wms][ 1050868 ] PanicStr.notInit ∗
      (n ↦[wms][ 1051817 ] [34] ∗ ((n ↦[i32][ 1051836 ] 1051836 ∗ n ↦[i32][ 1051836 + 4 ] 0) ∗
      (n ↦[i32][ 1055020 ] 116 ∗ (n ↦[i32][ 1057480 ] 123 ∗ (n ↦[wms][ 1061856 ] SerializeStr.esc ∗
      (n ↦[i32][ 1065416 ] 157 ∗ (n ↦[wms][ 1070974 ] FmtDigits.lut ∗ (n ↦[i32][ 1074896 ] 0 ∗
      ((n ↦[i32][ 1074900 ] 0 ∗ n ↦[i32][ 1074900 + 4 ] 0 ∗ n ↦[i32][ 1074900 + 8 ] 0 ∗ n ↦[i32][ 1074900 + 12 ] 0) ∗
      ((n ↦[i32][ 1074920 ] 0 ∗ n ↦[i32][ 1074920 + 4 ] 0 ∗ n ↦[i32][ 1074920 + 8 ] 0 ∗
        n ↦[i32][ 1074920 + 12 ] 0) ∗ True))))))))))))))))) := by
  have hL := hm.1
  refine cut n 0 L 1047840 736 (by omega) (by omega)
    ((memR_zero hm n 1047840 736 (Or.inr (by decide)) (by omega)).trans (zero_stk n 1047840 736)) ?_
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
  refine cut n _ _ 1051836 8 (by omega) (by omega) ((conv_data hm n 1051836 8 (by decide) (by decide) (by omega)
    seg_ts rfl).trans (bytes32_one_word n 1051836 1051836 0)) ?_
  refine cut n _ _ 1055020 4 (by omega) (by omega) (conv_data hm n 1055020 4 (by decide) (by decide) (by omega)
    seg_key116 rfl) ?_
  refine cut n _ _ 1057480 4 (by omega) (by omega) (conv_data hm n 1057480 4 (by decide) (by decide) (by omega)
    seg_vt rfl) ?_
  refine cut n _ _ 1061856 10 (by omega) (by omega) (conv_data hm n 1061856 10 (by decide) (by decide) (by omega)
    seg_esc rfl) ?_
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

theorem tablePt_addr {ta i j : Nat} {r : Ref} (h : i = j) : ta ↦[wt][ i ] r ⊢ (ta ↦[wt][ j ] r : IProp GF) := by
  subst h; exact .rfl

/-- The table entries `ft_total_supply` reaches through `call_indirect`: the interface's accessor
and initialiser (116, 106), the trampolines of `register_len`, `value_return`, `storage_read` and
`read_register` (39, 58, 82, 38), wee_alloc's `min_cell_size` (123), `u128`'s `Display::fmt` (157)
and the `fmt::Write` adapter's `write_str` (92); and the trampoline of `panic_utf8` (60), for the
panic path (`PanicStr`). -/
def tableRes (ta : Nat) : IProp GF :=
  iprop(ta ↦[wt][ 116 ] Ref.func 565 ∗ ta ↦[wt][ 106 ] Ref.func 564 ∗ ta ↦[wt][ 39 ] Ref.func 241 ∗
    ta ↦[wt][ 58 ] Ref.func 260 ∗ ta ↦[wt][ 82 ] Ref.func 284 ∗ ta ↦[wt][ 38 ] Ref.func 240 ∗
    ta ↦[wt][ 123 ] Ref.func 578 ∗ ta ↦[wt][ 157 ] Ref.func 759 ∗ ta ↦[wt][ 92 ] Ref.func 353 ∗
    ta ↦[wt][ 60 ] Ref.func 262)

set_option maxRecDepth 100000 in
/-- **The statics of `ft_total_supply`, with the panic path's** from the instantiated memory
(`MemImage`), its length `len` and limit 2048, and the table: the 736 bytes of stack below
1048576, `FtTotalSupply.statics` with the addresses of `wInst` (`A = id`), the default hook
(`old = 0`), the interface not set up (`k3 = 0`), wee_alloc's vtable index 123, `to_string`'s
pieces at 1051836, and the empty heap (`heapInv_init`); and the `panic_utf8` vtable slot
(`panicSlot`) and `PanicOnDefault`'s message. -/
theorem staticsResP {m : Memory} {L : Nat} (hm : MemImage m L) (n ta len : Nat) (hl1 : len % 65536 = 0)
    (hl0 : 0 < len) (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ tableRes ta ⊢
      stk n 1047840 736 ∗ FtTotalSupply.statics n ta id 0 0 123 1051836 2048 len ∗
        (PanicStr.panicSlot n ta id ∗ n ↦[wms][ 1050868 ] PanicStr.notInit) := by
  refine (sep_mono_left (memRes0 hm n)).trans ?_
  iintro ⟨⟨STK, KEY, V12, V16, V92, V100, V188, MSG, Q, ⟨TS0, TS4⟩, LK, VT, ESC, T157, LUT, HEAD,
    ⟨B0, B4, B8, B12⟩, ⟨K0, K4, K8, K12⟩, -⟩, HL, #HM, HT⟩
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

/-- **The statics of `ft_total_supply`** (`staticsResP`, the panic path's dropped). -/
theorem staticsRes {m : Memory} {L : Nat} (hm : MemImage m L) (n ta len : Nat) (hl1 : len % 65536 = 0) (hl0 : 0 < len)
    (hl2 : len < 2 ^ 32) :
    memR (GF := GF) m n 0 L ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some 2048 ∗ tableRes ta ⊢
      stk n 1047840 736 ∗ FtTotalSupply.statics n ta id 0 0 123 1051836 2048 len :=
  (staticsResP hm n ta len hl1 hl0 hl2).trans (sep_mono_right sep_elim_left)

end Mem

end WNear.Binary.InitialState
