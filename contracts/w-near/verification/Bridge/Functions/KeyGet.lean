import Binary.Code.Part09
import Binary.Code.Part10
import Bridge.Functions.BorrowMut

/-!
# `BLOCKCHAIN_INTERFACE::__getit` (565), on a fresh instance

The thread-local accessor `LocalKey::with` (463) reaches through
`call_indirect`: the `LocalKey` at 1055020 holds the table index 116, whose
entry is function 565. Below it, on the first access (the key's state word
at 1074900 zero, as in a fresh instance):

* `564` the initialiser `|| RefCell::new(None)`: the 8 bytes `0` (the borrow
  flag 0, the pointer of `None`) at `out` (3 instructions).
* `467` `statik::LazyStorage::initialize(key, init)`: `init` (a table index,
  106 for 564) run through `call_indirect` into a 48-byte frame; its 8 bytes
  moved to `key + 4`, the word after them (the vtable of the `None`, never
  written by `init`) to `key + 12`; the old contents and state (zero:
  nothing to drop) saved in the frame; the state set to 1; `key + 4`
  returned (58 instructions and the call, 70 in all).
* `468` `statik::Key::get(key, init)`: the state not 1, so `initialize`
  (9 instructions and the call, 90 in all).
* `565` `__getit()`: `Key::get(1074900, 106)` (3 instructions and the call,
  102 in all).

So the `RefCell<Option<Box<dyn BlockchainInterface>>>` lives at 1074904:
its borrow flag there, the box's data pointer at 1074908 and vtable at
1074912.
-/

namespace WNear.Binary.KeyGet

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.BorrowMut

/-! ## Two words as eight bytes -/

section Words

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem join64 (n i : Nat) (a b : UInt32) :
    memBytes (H := NearState) (GF := GF) n i (bytes32 a) ∗ n ↦[i32][ i + 4 ] b ⊢ n ↦[wms][ i ] (bytes32 a ++ bytes32 b) := by
  have e := memBytes_append (GF := GF) (H := NearState) n i (bytes32 a) (bytes32 b)
  rw [bytes32_length] at e
  exact e.2

theorem split64 (n i : Nat) (a b : UInt32) :
    memBytes (H := NearState) (GF := GF) n i (bytes32 a ++ bytes32 b) ⊢ n ↦[i32][ i ] a ∗ n ↦[i32][ i + 4 ] b := by
  have e := memBytes_append (GF := GF) (H := NearState) n i (bytes32 a) (bytes32 b)
  rw [bytes32_length] at e
  exact e.1

end Words

theorem storeBytes_i64_zero : storeBytes (.i64 0) 8 = bytes32 0 ++ bytes32 0 := rfl

theorem load64_zero : loadValue .i64 none (Memory.decodeLE (bytes32 0 ++ bytes32 0)) = .i64 0 :=
  rfl

/-! ## The initialiser (564) -/

section Init

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def initPre (n : Nat) (out w0 w1 : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out]⌝ ∗ n ↦[i32][ out.toNat ] w0 ∗ n ↦[i32][ out.toNat + 4 ] w1)

/-- `RefCell::new(None)`: the flag 0 and the null pointer. -/
def initPost (n : Nat) (out : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] 0)

theorem entryLocals_f564 (a : UInt32) : entryLocals f564 [.i32 a] = #[.i32 a] := rfl

/-- The initialiser (564): 3 instructions. -/
theorem f564_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out w0 w1 : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f564 Cg (initPre n out w0 w1)
      (fun _ => 3 * cfg.regularOpCost) (initPost n out) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold initPre at HP
  icases HP with ⟨%hargs, H0, H1⟩
  subst hargs
  ihave Hw := join64 n out.toNat w0 w1 $$ [H0 H1]
  · isplitl [H0] <;> iassumption
  rw [entryLocals_f564]
  simp only [f564]
  sstep; sstep; sstep [Hw]
  rw [storeBytes_i64_zero]
  icases split64 n out.toNat 0 0 $$ Hw with ⟨H0, H1⟩
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iunfold initPost
  iframe Hc H0 H1
  ipureintro; rfl

end Init


/-! ## `LazyStorage::initialize` (467), the state zero -/

section Initialize

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cells of a lazily initialised `static`, before its first access: the
state word zero, the value (the `RefCell`'s flag, the box's pointer and
vtable); and the 48-byte frame below `sp`, the words that `initialize`
touches; the stack pointer and the table entry of the initialiser. -/
def keyPreRes (n g ta a564 : Nat) (gi : GlobalInst) (sp key init k3 w0 w1 w8 f16 f20 f24 f28 : UInt32) :
    IProp GF :=
  iprop(g ↦[wg] gi ∗ ta ↦[wt][ init.toNat ] Ref.func a564 ∗
    n ↦[i32][ key.toNat ] 0 ∗ n ↦[i32][ key.toNat + 4 ] 0 ∗ n ↦[i32][ key.toNat + 8 ] 0 ∗
    n ↦[i32][ key.toNat + 12 ] k3 ∗
    n ↦[i32][ (sp - 48).toNat ] w0 ∗ n ↦[i32][ (sp - 48).toNat + 4 ] w1 ∗
    n ↦[i32][ (sp - 48).toNat + 8 ] w8 ∗ n ↦[i32][ (sp - 48).toNat + 16 ] f16 ∗
    n ↦[i32][ (sp - 48).toNat + 20 ] f20 ∗ n ↦[i32][ (sp - 48).toNat + 24 ] f24 ∗
    n ↦[i32][ (sp - 48).toNat + 28 ] f28)

/-- After: the state 1, the value `RefCell::new(None)` (the vtable word the
frame's garbage `w8`); the frame holding the old contents. -/
def keyPostRes (n g ta a564 : Nat) (gi : GlobalInst) (sp key init k3 w8 : UInt32) : IProp GF :=
  iprop(g ↦[wg] gi ∗ ta ↦[wt][ init.toNat ] Ref.func a564 ∗
    n ↦[i32][ key.toNat ] 1 ∗ n ↦[i32][ key.toNat + 4 ] 0 ∗ n ↦[i32][ key.toNat + 8 ] 0 ∗
    n ↦[i32][ key.toNat + 12 ] w8 ∗
    n ↦[i32][ (sp - 48).toNat ] 0 ∗ n ↦[i32][ (sp - 48).toNat + 4 ] 0 ∗
    n ↦[i32][ (sp - 48).toNat + 8 ] w8 ∗ n ↦[i32][ (sp - 48).toNat + 16 ] 0 ∗
    n ↦[i32][ (sp - 48).toNat + 20 ] 0 ∗ n ↦[i32][ (sp - 48).toNat + 24 ] 0 ∗
    n ↦[i32][ (sp - 48).toNat + 28 ] k3)

def keyPre (n g ta a564 : Nat) (gi : GlobalInst) (sp key init k3 w0 w1 w8 f16 f20 f24 f28 : UInt32)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 key, .i32 init]⌝ ∗
    keyPreRes n g ta a564 gi sp key init k3 w0 w1 w8 f16 f20 f24 f28)

def keyPost (n g ta a564 : Nat) (gi : GlobalInst) (sp key init k3 w8 : UInt32)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 (key + 4)]⌝ ∗ keyPostRes n g ta a564 gi sp key init k3 w8)

theorem entryLocals_f467 (a b : UInt32) :
    entryLocals f467 [.i32 a, .i32 b] = #[.i32 a, .i32 b, .i32 0, .i64 0, .i32 0] := rfl

theorem activation_f564 (c : Nat) (a : UInt32) :
    activationGas c (entryLocals f564 [.i32 a]) = 9 * c := by
  simp [activationGas, entryLocals, f564]

/-- `LazyStorage::initialize(key, init)` (467) on the first access: 58
instructions and the initialiser through `call_indirect` (its activation 9
and its 3), 70 in all. -/
theorem f467_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n g ta a564 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (hta : mi.tableAddrs[0]? = some ta) (ty564 : FuncType) (hty : ty564 = mi.types[0]!)
    (hty1 : ty564.params.length = 1) (hty2 : ty564.results = [])
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gi : GlobalInst) (sp : UInt32)
    (hgi : gi.value = .i32 sp) (hsp : 48 ≤ sp.toNat) (key init : UInt32)
    (hkey : key.toNat + 16 < 2 ^ 32) (k3 w0 w1 w8 f16 f20 f24 f28 : UInt32) :
    a564 ↪[wf] FuncInst.wasm ty564 inst f564 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f467 Cg
        (keyPre n g ta a564 gi sp key init k3 w0 w1 w8 f16 f20 f24 f28)
        (fun _ => 70 * cfg.regularOpCost) (keyPost n g ta a564 gi sp key init k3 w8) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold keyPre, keyPreRes at HP
  icases HP with ⟨%hargs, Hg, Ht, Hs, Hk1, Hk2, Hk3, H0, H1, H8, H16, H20, H24, H28⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp_all [UInt32.le_iff_toNat_le]
  have e8 : (sp - 48 + 8).toNat = (sp - 48).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have e28 : (sp - 48 + 16 + 12).toNat = (sp - 48).toNat + 28 := by
    simp [UInt32.toNat_add]; omega
  have e12 : (key + 12).toNat = key.toNat + 12 := by simp [UInt32.toNat_add]; omega
  rw [entryLocals_f467]
  simp only [f467]
  -- sp -= 48
  sstep [Hg]; sstep; sstep; sstep; sclean; sstep [Hg]
  -- init(sp)
  sstep; sstep; sclean
  iapply mwpi_cons
  iapply mwpi_call_indirect_spec_at (R := 50 * cfg.regularOpCost + R) (vs := [.i32 (sp - 48), .i32 init]) 0 0 ta init a564 ty564
    inst mi f564 [.i32 (sp - 48)] (initPre n (sp - 48) w0 w1) (fun _ => 3 * cfg.regularOpCost)
    (initPost n (sp - 48)) rfl hta hty (by simp [hty1]) hd
  isplitl [Hc]
  · rw [activation_f564]; scredits
  isplitl [Ht]; iexact Ht
  isplitr; iexact Hf
  isplitr; iexact Hi
  isplitr
  · iapply f564_spec cfg lim (d + 1) ty564 hty2 inst mi n hn Cg
  isplitl [H0 H1]
  · iunfold initPre
    iframe H0 H1
    ipureintro; rfl
  inext
  iintro %rs Ht Hc HQ
  iunfold initPost at HQ
  icases HQ with ⟨%hrs, H0, H1⟩
  subst hrs
  sclean
  -- the old value
  ihave Hk := join64 n (key.toNat + 4) 0 0 $$ [Hk1 Hk2]
  · isplitl [Hk1]
    · iexact Hk1
    · iapply (memBytes_congr (by omega)).1 $$ Hk2
  ihave Hw := join64 n (sp - 48).toNat 0 0 $$ [H0 H1]
  · isplitl [H0] <;> iassumption
  sstep; sstep [Hk]; rw [load64_zero]; sstep
  -- the new value
  sstep; sstep; sstep [Hw]; sclean; rw [load64_zero]; sstep [Hk]
  rw [storeBytes_i64_zero]
  -- the vtable word
  ihave Hk3 := (memBytes_congr e12.symm).1 $$ Hk3
  ihave H8 := (memBytes_congr e8.symm).1 $$ H8
  sstep; sstep; sstep; sstep; sstep [Hk3]; sclean; sstep
  sstep; sstep; sstep; sstep; sstep [H8]; sclean; sstep [Hk3]
  -- the state
  sstep; sstep [Hs]; sclean; sstep
  sstep; sstep; sstep [Hs]
  -- the old contents saved
  ihave H28 := (memBytes_congr e28.symm).1 $$ H28
  sstep; sstep; sstep; sstep; sstep; sstep; sstep [H28]
  sstep; sstep; sstep [H16]
  ihave Hf20 := join64 n ((sp - 48).toNat + 20) f20 f24 $$ [H20 H24]
  · isplitl [H20]
    · iexact H20
    · iapply (memBytes_congr (by omega)).1 $$ H24
  sstep; sstep; sclean; sstep [Hf20]
  rw [storeBytes_i64_zero]
  -- key + 4
  sstep; sstep; sstep; sstep; sclean
  -- nothing to drop
  sblock
  sstep; sstep; sclean
  sbr_taken
  spay
  -- sp += 48
  sstep; sstep; sstep; sstep [Hg]; sstep; sclean
  have e : sp - 48 + 48 = sp := by simp
  simp only [e]
  icases split64 n (key.toNat + 4) 0 0 $$ Hk with ⟨Hk1, Hk2⟩
  icases split64 n (sp - 48).toNat 0 0 $$ Hw with ⟨H0, H1⟩
  icases split64 n ((sp - 48).toNat + 20) 0 0 $$ Hf20 with ⟨H20, H24⟩
  ihave Hk2 := (memBytes_congr (j := key.toNat + 8) (by omega)).1 $$ Hk2
  ihave H24 := (memBytes_congr (j := (sp - 48).toNat + 24) (by omega)).1 $$ H24
  ihave Hk3 := (memBytes_congr e12).1 $$ Hk3
  ihave H8 := (memBytes_congr e8).1 $$ H8
  ihave H28 := (memBytes_congr e28).1 $$ H28
  unfold Post.mfunc
  simp only [htype]
  isplitr
  · ipureintro; simp
  iexists R
  isplitl [Hc]
  · scredits
  iintro Hc
  iframe Hc
  iunfold keyPost, keyPostRes
  iframe Hg Ht Hs Hk1 Hk2 Hk3 H0 H1 H8 H16 H20 H24 H28
  ipureintro; rfl

end Initialize


/-! ## `statik::Key::get` (468), the state zero -/

section KeyGetFn

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem entryLocals_f468 (a b : UInt32) :
    entryLocals f468 [.i32 a, .i32 b] = #[.i32 a, .i32 b] := rfl

theorem activation_f467 (c : Nat) (a b : UInt32) :
    activationGas c (entryLocals f467 [.i32 a, .i32 b]) = 11 * c := by
  simp [activationGas, entryLocals, f467, ValType.default]

/-- `Key::get(key, init)` (468) on the first access: 9 instructions and
`initialize` (its activation 11 and its 70), 90 in all. -/
theorem f468_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n g ta a564 a467 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (hta : mi.tableAddrs[0]? = some ta) (ha : mi.funcAddrs[467]? = some a467)
    (ty564 ty467 : FuncType) (hty : ty564 = mi.types[0]!)
    (hty1 : ty564.params.length = 1) (hty2 : ty564.results = [])
    (hty7 : ty467.params.length = 2) (hty7' : ty467.results.length = 1)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gi : GlobalInst) (sp : UInt32)
    (hgi : gi.value = .i32 sp) (hsp : 48 ≤ sp.toNat) (key init : UInt32)
    (hkey : key.toNat + 16 < 2 ^ 32) (k3 w0 w1 w8 f16 f20 f24 f28 : UInt32) :
    a467 ↪[wf] FuncInst.wasm ty467 inst f467 ∗ a564 ↪[wf] FuncInst.wasm ty564 inst f564 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f468 Cg
        (keyPre n g ta a564 gi sp key init k3 w0 w1 w8 f16 f20 f24 f28)
        (fun _ => 90 * cfg.regularOpCost) (keyPost n g ta a564 gi sp key init k3 w8) := by
  iintro ⟨#Hf7, #Hf4, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold keyPre, keyPreRes at HP
  icases HP with ⟨%hargs, Hg, Ht, Hs, Hk1, Hk2, Hk3, H0, H1, H8, H16, H20, H24, H28⟩
  subst hargs
  rw [entryLocals_f468]
  simp only [f468]
  sblock
  sstep; sstep [Hs]; sclean; sstep; sstep
  sbr_not
  sstep; sstep; sclean
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 1 * cfg.regularOpCost + R) 467 a467 ty467 inst mi f467
    [.i32 key, .i32 init] (keyPre n g ta a564 gi sp key init k3 w0 w1 w8 f16 f20 f24 f28)
    (fun _ => 70 * cfg.regularOpCost) (keyPost n g ta a564 gi sp key init k3 w8) ha
    (by simp [hty7]) (by omega)
  isplitl [Hc]
  · rw [activation_f467]; scredits
  isplitr; iexact Hf7
  isplitr; iexact Hi
  isplitr
  · iapply f467_spec cfg lim (d + 1) ty467 hty7' inst mi n g ta a564 hn hg hta ty564 hty hty1
      hty2 (by omega) Cg gi sp hgi hsp key init hkey k3 w0 w1 w8 f16 f20 f24 f28
    iframe Hf4 Hi
  isplitl [Hg Ht Hs Hk1 Hk2 Hk3 H0 H1 H8 H16 H20 H24 H28]
  · iunfold keyPre, keyPreRes
    iframe Hg Ht Hs Hk1 Hk2 Hk3 H0 H1 H8 H16 H20 H24 H28
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold keyPost at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  sclean
  iapply mwpi_return
  sclean
  unfold Post.mfunc
  simp only [htype]
  isplitr
  · ipureintro; simp
  iexists R
  isplitl [Hc]
  · scredits
  iintro Hc
  iframe Hc
  iunfold keyPost
  iframe HQ
  ipureintro; rfl

end KeyGetFn

/-! ## `BLOCKCHAIN_INTERFACE::__getit` (565), the first access -/

section GetIt

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key at 1074900, its initialiser at table index 106. -/
def getItPre (n g ta a564 : Nat) (gi : GlobalInst) (sp k3 w0 w1 w8 f16 f20 f24 f28 : UInt32)
    (args : List Value) : IProp GF :=
  iprop(⌜args = []⌝ ∗ keyPreRes n g ta a564 gi sp 1074900 106 k3 w0 w1 w8 f16 f20 f24 f28)

/-- The `RefCell` at 1074904 returned. -/
def getItPost (n g ta a564 : Nat) (gi : GlobalInst) (sp k3 w8 : UInt32) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = [.i32 1074904]⌝ ∗ keyPostRes n g ta a564 gi sp 1074900 106 k3 w8)

theorem entryLocals_f565 : entryLocals f565 [] = #[] := rfl

theorem activation_f468 (c : Nat) (a b : UInt32) :
    activationGas c (entryLocals f468 [.i32 a, .i32 b]) = 9 * c := by
  simp [activationGas, entryLocals, f468]

/-- `__getit()` (565) on the first access: 3 instructions and `Key::get`
(its activation 9 and its 90), 102 in all. -/
theorem f565_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst)
    (n g ta a564 a467 a468 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (hta : mi.tableAddrs[0]? = some ta) (ha7 : mi.funcAddrs[467]? = some a467)
    (ha8 : mi.funcAddrs[468]? = some a468)
    (ty564 ty467 ty468 : FuncType) (hty : ty564 = mi.types[0]!)
    (hty1 : ty564.params.length = 1) (hty2 : ty564.results = [])
    (hty7 : ty467.params.length = 2) (hty7' : ty467.results.length = 1)
    (hty8 : ty468.params.length = 2) (hty8' : ty468.results.length = 1)
    (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (gi : GlobalInst) (sp : UInt32)
    (hgi : gi.value = .i32 sp) (hsp : 48 ≤ sp.toNat) (k3 w0 w1 w8 f16 f20 f24 f28 : UInt32) :
    a468 ↪[wf] FuncInst.wasm ty468 inst f468 ∗ a467 ↪[wf] FuncInst.wasm ty467 inst f467 ∗
      a564 ↪[wf] FuncInst.wasm ty564 inst f564 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f565 Cg
        (getItPre n g ta a564 gi sp k3 w0 w1 w8 f16 f20 f24 f28)
        (fun _ => 102 * cfg.regularOpCost) (getItPost n g ta a564 gi sp k3 w8) := by
  iintro ⟨#Hf8, #Hf7, #Hf4, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold getItPre at HP
  icases HP with ⟨%hargs, HR⟩
  subst hargs
  rw [entryLocals_f565]
  simp only [f565]
  sstep; sstep
  iapply mwpi_call_spec_args (R := R) 468 a468 ty468 inst mi f468
    [.i32 1074900, .i32 106] (keyPre n g ta a564 gi sp 1074900 106 k3 w0 w1 w8 f16 f20 f24 f28)
    (fun _ => 90 * cfg.regularOpCost) (keyPost n g ta a564 gi sp 1074900 106 k3 w8) ha8
    (by simp [hty8]) (by omega)
  isplitl [Hc]
  · rw [activation_f468]; scredits
  isplitr; iexact Hf8
  isplitr; iexact Hi
  isplitr
  · iapply f468_spec cfg lim (d + 1) ty468 hty8' inst mi n g ta a564 a467 hn hg hta ha7 ty564
      ty467 hty hty1 hty2 hty7 hty7' (by omega) Cg gi sp hgi hsp 1074900 106 (by decide)
      k3 w0 w1 w8 f16 f20 f24 f28
    iframe Hf7 Hf4 Hi
  isplitl [HR]
  · iunfold keyPre
    iframe HR
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold keyPost at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  unfold Post.mfunc
  simp only [htype]
  isplitr
  · ipureintro; simp
  iexists R
  iframe Hc
  iintro Hc
  iframe Hc
  iunfold getItPost
  iframe HQ
  ipureintro; rfl

end GetIt

end WNear.Binary.KeyGet
