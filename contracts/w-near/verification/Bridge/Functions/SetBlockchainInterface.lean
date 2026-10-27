import Binary.Code.Part09
import Binary.Code.Part10
import Bridge.Functions.KeyGet

/-!
# `env::set_blockchain_interface` (function 520), in the metered logic

`set_blockchain_interface(b: Box<dyn BlockchainInterface>)` is
`BLOCKCHAIN_INTERFACE.with(|cell| *cell.borrow_mut() = Some(b))`:

```wat
i32.const 1055020  local.get 0  local.get 1  call 463   ;; LocalKey::with(&KEY, data, vtable)
```

`463` `LocalKey::with(key, data, vtable)`, on the path a fresh instance
takes, in a 32-byte frame below `sp`:

* the closure `(data, vtable)` saved in the frame;
* the accessor (the table index 116 at `key`, function 565, through
  `call_indirect`; `KeyGet.lean`) initialises the thread-local
  `RefCell<Option<Box<dyn _>>>` at 1074904 to `RefCell::new(None)` and
  returns it (not null);
* `RefCell::borrow_mut` (441) takes the flag (-1) and writes the `RefMut`
  (value 1074908, flag 1074904) in the frame; the old value, `None`, dropped
  (464: nothing); `(data, vtable)` written at 1074908/1074912; the `RefMut`
  dropped (442: the flag back to 0);
* `Result::expect` (433) on `Ok`.

55 instructions and the calls (565: activation 8 and 102; 441: 11 and 59;
464: 9 and 4; 442: 9 and 26; 433: 9 and 12), 304 in all; 520 adds 4
instructions and 463's activation 10: 318.

So `set_blockchain_interface(data, vtable)` leaves the static cells
`blockchainInterfaceCells n 1 0 data vtable`: the key initialised (state 1),
the `RefCell` free (flag 0) holding `Some((data, vtable))`. The contract
calls it with `(1, 1050188)` (`Box::new(VmBlockchainInterface)`, a
zero-sized box): that points-to is "the blockchain interface set up".
-/

namespace WNear.Binary.SetBlockchainInterface

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.BorrowMut
open WNear.Binary.KeyGet

section Cells

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The thread-local `BLOCKCHAIN_INTERFACE`: its lazy state at 1074900, then
the `RefCell<Option<Box<dyn BlockchainInterface>>>`: the borrow flag, the
box's data pointer (0 for `None`) and vtable. -/
def blockchainInterfaceCells (n : Nat) (state flag data vtable : UInt32) : IProp GF :=
  iprop(n ↦[i32][ 1074900 ] state ∗ n ↦[i32][ 1074904 ] flag ∗ n ↦[i32][ 1074908 ] data ∗
    n ↦[i32][ 1074912 ] vtable)

/-- The words of the frames below `sp` written on the way: `LocalKey::with`'s
(at `sp - 32`) and `LazyStorage::initialize`'s (at `sp - 32 - 48`). -/
def frames (n : Nat) (sp u8 u12 u16 u20 u24 u28 w0 w1 w8 f16 f20 f24 f28 : UInt32) : IProp GF :=
  iprop(n ↦[i32][ (sp - 32).toNat + 8 ] u8 ∗ n ↦[i32][ (sp - 32).toNat + 12 ] u12 ∗
    n ↦[i32][ (sp - 32).toNat + 16 ] u16 ∗ n ↦[i32][ (sp - 32).toNat + 20 ] u20 ∗
    n ↦[i32][ (sp - 32).toNat + 24 ] u24 ∗ n ↦[i32][ (sp - 32).toNat + 28 ] u28 ∗
    n ↦[i32][ (sp - 32 - 48).toNat ] w0 ∗ n ↦[i32][ (sp - 32 - 48).toNat + 4 ] w1 ∗
    n ↦[i32][ (sp - 32 - 48).toNat + 8 ] w8 ∗ n ↦[i32][ (sp - 32 - 48).toNat + 16 ] f16 ∗
    n ↦[i32][ (sp - 32 - 48).toNat + 20 ] f20 ∗ n ↦[i32][ (sp - 32 - 48).toNat + 24 ] f24 ∗
    n ↦[i32][ (sp - 32 - 48).toNat + 28 ] f28)

end Cells

/-! ## `LocalKey::with` (463) -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The stack pointer, the key (the accessor's table index 116), the table
entries of the accessor and of the initialiser, the static cells before the
first access, and the frames. -/
def withPre (n g ta a564 a565 : Nat) (gi : GlobalInst) (sp key data vtable k3 u8 u12 u16 u20 u24 u28
    w0 w1 w8 f16 f20 f24 f28 : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 key, .i32 data, .i32 vtable]⌝ ∗ g ↦[wg] gi ∗ n ↦[i32][ key.toNat ] 116 ∗
    ta ↦[wt][ 116 ] Ref.func a565 ∗ ta ↦[wt][ 106 ] Ref.func a564 ∗
    blockchainInterfaceCells n 0 0 0 k3 ∗
    frames n sp u8 u12 u16 u20 u24 u28 w0 w1 w8 f16 f20 f24 f28)

/-- The interface set: the key initialised, the cell free, holding
`Some((data, vtable))`. -/
def withPost (n g ta a564 a565 : Nat) (gi : GlobalInst) (sp key data vtable k3 w8 : UInt32)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ n ↦[i32][ key.toNat ] 116 ∗
    ta ↦[wt][ 116 ] Ref.func a565 ∗ ta ↦[wt][ 106 ] Ref.func a564 ∗
    blockchainInterfaceCells n 1 0 data vtable ∗
    frames n sp 1074908 1074904 data vtable 1074908 1074904 0 0 w8 0 0 0 k3)

theorem entryLocals_f463 (a b c : UInt32) :
    entryLocals f463 [.i32 a, .i32 b, .i32 c] = #[.i32 a, .i32 b, .i32 c, .i32 0] := rfl

theorem activation_f565 (c : Nat) : activationGas c (entryLocals f565 []) = 8 * c := by
  simp [activationGas, entryLocals, f565]

theorem activation_f441 (c : Nat) (a b e : UInt32) :
    activationGas c (entryLocals f441 [.i32 a, .i32 b, .i32 e]) = 11 * c := by
  simp [activationGas, entryLocals, f441, ValType.default]

theorem activation_f464 (c : Nat) (a : UInt32) :
    activationGas c (entryLocals f464 [.i32 a]) = 9 * c := by
  simp [activationGas, entryLocals, f464]

theorem activation_f442 (c : Nat) (a : UInt32) :
    activationGas c (entryLocals f442 [.i32 a]) = 9 * c := by
  simp [activationGas, entryLocals, f442]

theorem activation_f433 (c : Nat) (a : UInt32) :
    activationGas c (entryLocals f433 [.i32 a]) = 9 * c := by
  simp [activationGas, entryLocals, f433, ValType.default]

theorem or_four (x : UInt32) (h : x.toNat % 8 = 0) (hb : x.toNat + 28 < 2 ^ 32) :
    (x + 24) ||| 4 = x + 28 := by
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_or, UInt32.toNat_add, UInt32.reduceToNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := 4) (by decide) ((x.toNat + 24) / 8)
  have m : 2 ^ 3 * ((x.toNat + 24) / 8) = x.toNat + 24 := by omega
  rw [m] at e
  omega

/-- `LocalKey::with(key, data, vtable)` (463) storing `Some((data, vtable))`
in `BLOCKCHAIN_INTERFACE` on its first access: 55 instructions and the
calls, 304 in all. -/
theorem f463_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst)
    (n g ta a564 a565 a467 a468 a441 a492 a672 a464 a442 a433 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (hta : mi.tableAddrs[0]? = some ta)
    (ha467 : mi.funcAddrs[467]? = some a467) (ha468 : mi.funcAddrs[468]? = some a468)
    (ha441 : mi.funcAddrs[441]? = some a441) (ha492 : mi.funcAddrs[492]? = some a492)
    (ha672 : mi.funcAddrs[672]? = some a672) (ha464 : mi.funcAddrs[464]? = some a464)
    (ha442 : mi.funcAddrs[442]? = some a442) (ha433 : mi.funcAddrs[433]? = some a433)
    (ty564 ty565 ty467 ty468 ty441 ty492 ty672 ty464 ty442 ty433 : FuncType)
    (hty564 : ty564 = mi.types[0]!) (hty564a : ty564.params.length = 1)
    (hty564b : ty564.results = [])
    (hty565 : ty565 = mi.types[1]!) (hty565a : ty565.params.length = 0)
    (hty565b : ty565.results.length = 1)
    (hty467a : ty467.params.length = 2) (hty467b : ty467.results.length = 1)
    (hty468a : ty468.params.length = 2) (hty468b : ty468.results.length = 1)
    (hty441a : ty441.params.length = 3) (hty441b : ty441.results = [])
    (hty492a : ty492.params.length = 1) (hty492b : ty492.results.length = 1)
    (hty672a : ty672.params.length = 2) (hty672b : ty672.results.length = 1)
    (hty464a : ty464.params.length = 1) (hty464b : ty464.results = [])
    (hty442a : ty442.params.length = 1) (hty442b : ty442.results = [])
    (hty433a : ty433.params.length = 1) (hty433b : ty433.results = [])
    (hd : d + 4 < lim.maxCallDepth) (Cg : Nat) (gi : GlobalInst) (sp : UInt32)
    (hgi : gi.value = .i32 sp) (hsp : 80 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (key data vtable k3 u8 u12 u16 u20 u24 u28 w0 w1 w8 f16 f20 f24 f28 : UInt32) :
    a565 ↪[wf] FuncInst.wasm ty565 inst f565 ∗ a468 ↪[wf] FuncInst.wasm ty468 inst f468 ∗
      a467 ↪[wf] FuncInst.wasm ty467 inst f467 ∗ a564 ↪[wf] FuncInst.wasm ty564 inst f564 ∗
      a441 ↪[wf] FuncInst.wasm ty441 inst f441 ∗ a492 ↪[wf] FuncInst.wasm ty492 inst f492 ∗
      a672 ↪[wf] FuncInst.wasm ty672 inst f672 ∗ a464 ↪[wf] FuncInst.wasm ty464 inst f464 ∗
      a442 ↪[wf] FuncInst.wasm ty442 inst f442 ∗ a433 ↪[wf] FuncInst.wasm ty433 inst f433 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f463 Cg
        (withPre n g ta a564 a565 gi sp key data vtable k3 u8 u12 u16 u20 u24 u28
          w0 w1 w8 f16 f20 f24 f28)
        (fun _ => 304 * cfg.regularOpCost)
        (withPost n g ta a564 a565 gi sp key data vtable k3 w8) := by
  iintro ⟨#Hf565, #Hf468, #Hf467, #Hf564, #Hf441, #Hf492, #Hf672, #Hf464, #Hf442, #Hf433, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, Hkey, Ht116, Ht106, HC, HF⟩
  iunfold blockchainInterfaceCells at HC
  iunfold frames at HF
  icases HC with ⟨Hs, Hfl, Hda, Hvt⟩
  icases HF with ⟨U8, U12, U16, U20, U24, U28, W0, W1, W8, F16, F20, F24, F28⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have e28 : (sp - 32 + 28).toNat = (sp - 32).toNat + 28 := by simp [UInt32.toNat_add]; omega
  have hor : (sp - 32 + 24) ||| 4 = sp - 32 + 28 := or_four _ (by omega) (by omega)
  rw [entryLocals_f463]
  simp only [f463]
  -- sp -= 32; the closure saved
  sstep [Hg]; sstep; sstep; sstep; sclean; sstep [Hg]
  sstep; sstep; sstep [U20]
  sstep; sstep; sstep [U16]
  sblock; sblock
  -- the accessor
  sstep; sstep [Hkey]; sclean
  iapply mwpi_cons
  iapply mwpi_call_indirect_spec_at (R := 180 * cfg.regularOpCost + R) (vs := [.i32 116]) 1 0 ta
    116 a565 ty565 inst mi f565 [] (getItPre n g ta a564 { type := gt, value := .i32 (sp - 32) }
      (sp - 32) k3 w0 w1 w8 f16 f20 f24 f28) (fun _ => 102 * cfg.regularOpCost)
    (getItPost n g ta a564 { type := gt, value := .i32 (sp - 32) } (sp - 32) k3 w8) rfl hta
    hty565 (by simp [hty565a]) (by omega)
  isplitl [Hc]
  · rw [activation_f565]; scredits
  isplitl [Ht116]
  · simp only [UInt32.reduceToNat]; iexact Ht116
  isplitr; iexact Hf565
  isplitr; iexact Hi
  isplitr
  · iapply f565_spec cfg lim (d + 1) ty565 hty565b inst mi n g ta a564 a467 a468 hn hg hta ha467
      ha468 ty564 ty467 ty468 hty564 hty564a hty564b hty467a hty467b hty468a hty468b (by omega) Cg
      { type := gt, value := .i32 (sp - 32) } (sp - 32) rfl (by omega) k3 w0 w1 w8 f16 f20 f24 f28
    iframe Hf468 Hf467 Hf564 Hi
  isplitl [Hg Ht106 Hs Hfl Hda Hvt W0 W1 W8 F16 F20 F24 F28]
  · iunfold getItPre, keyPreRes
    simp only [UInt32.reduceToNat]
    iframe Hg Ht106 Hs Hfl Hda Hvt W0 W1 W8 F16 F20 F24 F28
  inext
  iintro %rs Ht116 Hc HQ
  iunfold getItPost, keyPostRes at HQ
  icases HQ with ⟨%hrs, Hg, Ht106, Hs, Hfl, Hda, Hvt, W0, W1, W8, F16, F20, F24, F28⟩
  subst hrs
  simp only [UInt32.reduceToNat]
  sclean
  sstep; sstep; sclean
  sbr_not
  -- borrow_mut
  sstep; sstep; sstep; sstep; sstep; sclean
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 101 * cfg.regularOpCost + R) 441 a441 ty441 inst mi f441
    [.i32 (sp - 32 + 8), .i32 1074904, .i32 1055120]
    (borrowMutPre n g { type := gt, value := .i32 (sp - 32) } (sp - 32 + 8) 1074904 1055120 u8 u12)
    (fun _ => 59 * cfg.regularOpCost)
    (borrowMutPost n g { type := gt, value := .i32 (sp - 32) } (sp - 32 + 8) 1074904) ha441
    (by simp [hty441a]) (by omega)
  isplitl [Hc]
  · rw [activation_f441]; scredits
  isplitr; iexact Hf441
  isplitr; iexact Hi
  isplitr
  · iapply f441_spec cfg lim (d + 1) ty441 hty441b inst mi n g a492 a672 hn hg ha492 ha672 ty492
      ty672 hty492a hty492b hty672a hty672b (by omega) Cg { type := gt, value := .i32 (sp - 32) }
      (sp - 32) rfl (sp - 32 + 8) 1074904 1055120 u8 u12 (by decide)
    iframe Hf492 Hf672 Hi
  isplitl [Hg Hfl U8 U12]
  · iunfold borrowMutPre
    simp only [UInt32.reduceToNat, e8, Nat.add_assoc, Nat.reduceAdd]
    iframe Hg Hfl U8 U12
  inext
  iintro %rs Hc HQ
  iunfold borrowMutPost at HQ
  icases HQ with ⟨%hrs, Hg, Hfl, U8, U12⟩
  subst hrs
  simp only [UInt32.reduceToNat, e8, Nat.add_assoc, Nat.reduceAdd, UInt32.reduceAdd]
  sclean
  -- the RefMut in the frame
  sstep; sstep; sstep [U12]; sclean; sstep [U28]
  sstep; sstep; sstep [U8]; sclean; sstep; sstep [U24]
  -- the old value: None
  sstep; sclean
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 77 * cfg.regularOpCost + R) 464 a464 ty464 inst mi f464
    [.i32 1074908] (dropNonePre n 1074908) (fun _ => 4 * cfg.regularOpCost)
    (dropNonePost n 1074908) ha464 (by simp [hty464a]) (by omega)
  isplitl [Hc]
  · rw [activation_f464]; scredits
  isplitr; iexact Hf464
  isplitr; iexact Hi
  isplitr
  · iapply f464_spec cfg lim (d + 1) ty464 hty464b inst mi n hn Cg
  isplitl [Hda]
  · iunfold dropNonePre
    simp only [UInt32.reduceToNat]
    iframe Hda
  inext
  iintro %rs Hc HQ
  iunfold dropNonePost at HQ
  icases HQ with ⟨%hrs, Hda⟩
  subst hrs
  simp only [UInt32.reduceToNat]
  sclean
  -- Some((data, vtable))
  ihave Hvt := (memBytes_congr (i := 1074912) (j := (1074908 : UInt32).toNat + 4) (by simp)).1 $$ Hvt
  ihave Hda := (memBytes_congr (i := 1074908) (j := (1074908 : UInt32).toNat + 0) (by simp)).1 $$ Hda
  sstep; sstep; sstep [Hvt]
  sstep; sstep; sstep [Hda]
  -- the RefMut dropped
  sstep; sstep; sstep; sstep; sstep; sclean
  rw [hor]
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 30 * cfg.regularOpCost + R) 442 a442 ty442 inst mi f442
    [.i32 (sp - 32 + 28)] (dropPre n (sp - 32 + 28) 1074904 4294967295) (fun _ => 26 * cfg.regularOpCost)
    (dropPost n (sp - 32 + 28) 1074904 4294967295) ha442 (by simp [hty442a]) (by omega)
  isplitl [Hc]
  · rw [activation_f442]; scredits
  isplitr; iexact Hf442
  isplitr; iexact Hi
  isplitr
  · iapply f442_spec cfg lim (d + 1) ty442 hty442b inst mi n a672 hn ha672 ty672 hty672a hty672b
      (by omega) Cg (sp - 32 + 28) 1074904 4294967295
    iframe Hf672 Hi
  isplitl [U28 Hfl]
  · iunfold dropPre
    simp only [UInt32.reduceToNat, e28]
    iframe U28 Hfl
  inext
  iintro %rs Hc HQ
  iunfold dropPost at HQ
  icases HQ with ⟨%hrs, U28, Hfl⟩
  subst hrs
  simp only [UInt32.reduceToNat, UInt32.reduceAdd, e28]
  sclean
  -- Ok(())
  sstep; sstep; sclean
  iapply mwpi_br
  sclean
  spay
  sstep; sclean
  iapply mwpi_cons
  iapply mwpi_call_spec_args (R := 4 * cfg.regularOpCost + R) 433 a433 ty433 inst mi f433
    [.i32 0] (expectPre g { type := gt, value := .i32 (sp - 32) }) (fun _ => 12 * cfg.regularOpCost)
    (expectPost g { type := gt, value := .i32 (sp - 32) }) ha433 (by simp [hty433a]) (by omega)
  isplitl [Hc]
  · rw [activation_f433]; scredits
  isplitr; iexact Hf433
  isplitr; iexact Hi
  isplitr
  · iapply f433_spec cfg lim (d + 1) ty433 hty433b inst mi g hg Cg
      { type := gt, value := .i32 (sp - 32) } (sp - 32) rfl
  isplitl [Hg]
  · iunfold expectPre
    iframe Hg
    ipureintro; rfl
  inext
  iintro %rs Hc HQ
  iunfold expectPost at HQ
  icases HQ with ⟨%hrs, Hg⟩
  subst hrs
  sclean
  -- sp += 32
  sstep; sstep; sstep; sstep [Hg]
  have e : sp - 32 + 32 = sp := by simp
  simp only [e]
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  isplitl [Hc]
  · scredits
  iintro Hc
  iframe Hc
  iunfold withPost, blockchainInterfaceCells, frames
  iframe Hg Hkey Ht116 Ht106 Hs Hfl Hda Hvt U8 U12 U16 U20 U24 U28 W0 W1 W8 F16 F20 F24 F28
  ipureintro; rfl

end With

/-! ## `env::set_blockchain_interface` (520) -/

section SetBlockchainInterface

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The stack pointer, the `LocalKey` at 1055020 (the accessor's table
index 116), the table entries of the accessor (565) and of the initialiser
(564), `BLOCKCHAIN_INTERFACE`'s cells as in a fresh instance (not yet
accessed: state, flag and pointer zero) and the frames below `sp`. -/
def pre (n g ta a564 a565 : Nat) (gi : GlobalInst) (sp data vtable k3 u8 u12 u16 u20 u24 u28
    w0 w1 w8 f16 f20 f24 f28 : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 data, .i32 vtable]⌝ ∗ g ↦[wg] gi ∗ n ↦[i32][ 1055020 ] 116 ∗
    ta ↦[wt][ 116 ] Ref.func a565 ∗ ta ↦[wt][ 106 ] Ref.func a564 ∗
    blockchainInterfaceCells n 0 0 0 k3 ∗
    frames n sp u8 u12 u16 u20 u24 u28 w0 w1 w8 f16 f20 f24 f28)

/-- The blockchain interface set: `BLOCKCHAIN_INTERFACE` initialised (state
1), its `RefCell` free (flag 0) holding `Some(Box(data, vtable))`. -/
def post (n g ta a564 a565 : Nat) (gi : GlobalInst) (sp data vtable k3 w8 : UInt32)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ n ↦[i32][ 1055020 ] 116 ∗
    ta ↦[wt][ 116 ] Ref.func a565 ∗ ta ↦[wt][ 106 ] Ref.func a564 ∗
    blockchainInterfaceCells n 1 0 data vtable ∗
    frames n sp 1074908 1074904 data vtable 1074908 1074904 0 0 w8 0 0 0 k3)

theorem entryLocals_f520 (a b : UInt32) : entryLocals f520 [.i32 a, .i32 b] = #[.i32 a, .i32 b] :=
  rfl

theorem activation_f463 (c : Nat) (a b e : UInt32) :
    activationGas c (entryLocals f463 [.i32 a, .i32 b, .i32 e]) = 10 * c := by
  simp [activationGas, entryLocals, f463, ValType.default]

/-- `env::set_blockchain_interface(data, vtable)` (function 520 of
`contract.wasm`), on a fresh instance's `BLOCKCHAIN_INTERFACE`: 4
instructions and `LocalKey::with` (its activation 10 and its 304), 318 in
all. -/
theorem f520_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst)
    (n g ta a564 a565 a467 a468 a463 a441 a492 a672 a464 a442 a433 : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g)
    (hta : mi.tableAddrs[0]? = some ta)
    (ha467 : mi.funcAddrs[467]? = some a467) (ha468 : mi.funcAddrs[468]? = some a468)
    (ha463 : mi.funcAddrs[463]? = some a463)
    (ha441 : mi.funcAddrs[441]? = some a441) (ha492 : mi.funcAddrs[492]? = some a492)
    (ha672 : mi.funcAddrs[672]? = some a672) (ha464 : mi.funcAddrs[464]? = some a464)
    (ha442 : mi.funcAddrs[442]? = some a442) (ha433 : mi.funcAddrs[433]? = some a433)
    (ty564 ty565 ty467 ty468 ty463 ty441 ty492 ty672 ty464 ty442 ty433 : FuncType)
    (hty564 : ty564 = mi.types[0]!) (hty564a : ty564.params.length = 1)
    (hty564b : ty564.results = [])
    (hty565 : ty565 = mi.types[1]!) (hty565a : ty565.params.length = 0)
    (hty565b : ty565.results.length = 1)
    (hty467a : ty467.params.length = 2) (hty467b : ty467.results.length = 1)
    (hty468a : ty468.params.length = 2) (hty468b : ty468.results.length = 1)
    (hty463a : ty463.params.length = 3) (hty463b : ty463.results = [])
    (hty441a : ty441.params.length = 3) (hty441b : ty441.results = [])
    (hty492a : ty492.params.length = 1) (hty492b : ty492.results.length = 1)
    (hty672a : ty672.params.length = 2) (hty672b : ty672.results.length = 1)
    (hty464a : ty464.params.length = 1) (hty464b : ty464.results = [])
    (hty442a : ty442.params.length = 1) (hty442b : ty442.results = [])
    (hty433a : ty433.params.length = 1) (hty433b : ty433.results = [])
    (hd : d + 5 < lim.maxCallDepth) (Cg : Nat) (gi : GlobalInst) (sp : UInt32)
    (hgi : gi.value = .i32 sp) (hsp : 80 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (data vtable k3 u8 u12 u16 u20 u24 u28 w0 w1 w8 f16 f20 f24 f28 : UInt32) :
    a463 ↪[wf] FuncInst.wasm ty463 inst f463 ∗
      a565 ↪[wf] FuncInst.wasm ty565 inst f565 ∗ a468 ↪[wf] FuncInst.wasm ty468 inst f468 ∗
      a467 ↪[wf] FuncInst.wasm ty467 inst f467 ∗ a564 ↪[wf] FuncInst.wasm ty564 inst f564 ∗
      a441 ↪[wf] FuncInst.wasm ty441 inst f441 ∗ a492 ↪[wf] FuncInst.wasm ty492 inst f492 ∗
      a672 ↪[wf] FuncInst.wasm ty672 inst f672 ∗ a464 ↪[wf] FuncInst.wasm ty464 inst f464 ∗
      a442 ↪[wf] FuncInst.wasm ty442 inst f442 ∗ a433 ↪[wf] FuncInst.wasm ty433 inst f433 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f520 Cg
        (pre n g ta a564 a565 gi sp data vtable k3 u8 u12 u16 u20 u24 u28 w0 w1 w8 f16 f20 f24 f28)
        (fun _ => 318 * cfg.regularOpCost) (post n g ta a564 a565 gi sp data vtable k3 w8) := by
  iintro ⟨#Hf463, #Hf565, #Hf468, #Hf467, #Hf564, #Hf441, #Hf492, #Hf672, #Hf464, #Hf442,
    #Hf433, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, Hkey, Ht116, Ht106, HC, HF⟩
  subst hargs
  rw [entryLocals_f520]
  simp only [f520]
  sstep; sstep; sstep; sclean
  iapply mwpi_call_spec_args (R := R) 463 a463 ty463 inst mi f463
    [.i32 1055020, .i32 data, .i32 vtable]
    (withPre n g ta a564 a565 gi sp 1055020 data vtable k3 u8 u12 u16 u20 u24 u28
      w0 w1 w8 f16 f20 f24 f28) (fun _ => 304 * cfg.regularOpCost)
    (withPost n g ta a564 a565 gi sp 1055020 data vtable k3 w8) ha463 (by simp [hty463a])
    (by omega)
  isplitl [Hc]
  · rw [activation_f463]; scredits
  isplitr; iexact Hf463
  isplitr; iexact Hi
  isplitr
  · iapply f463_spec cfg lim (d + 1) ty463 hty463b inst mi n g ta a564 a565 a467 a468 a441 a492
      a672 a464 a442 a433 hn hg hta ha467 ha468 ha441 ha492 ha672 ha464 ha442 ha433 ty564 ty565
      ty467 ty468 ty441 ty492 ty672 ty464 ty442 ty433 hty564 hty564a hty564b hty565 hty565a
      hty565b hty467a hty467b hty468a hty468b hty441a hty441b hty492a hty492b hty672a hty672b
      hty464a hty464b hty442a hty442b hty433a hty433b (by omega) Cg gi sp hgi hsp hal
      1055020 data vtable k3 u8 u12 u16 u20 u24 u28 w0 w1 w8 f16 f20 f24 f28
    iframe Hf565 Hf468 Hf467 Hf564 Hf441 Hf492 Hf672 Hf464 Hf442 Hf433 Hi
  isplitl [Hg Hkey Ht116 Ht106 HC HF]
  · iunfold withPre
    simp only [UInt32.reduceToNat]
    iframe Hg Hkey Ht116 Ht106 HC HF
  inext
  iintro %rs Hc HQ
  iunfold withPost at HQ
  icases HQ with ⟨%hrs, Hg, Hkey, Ht116, Ht106, HC, HF⟩
  subst hrs
  simp only [UInt32.reduceToNat]
  unfold Post.mfunc
  simp only [htype, List.length_nil]
  isplitr
  · ipureintro; exact Nat.zero_le _
  iexists R
  iframe Hc
  iintro Hc
  iframe Hc
  iunfold post
  iframe Hg Hkey Ht116 Ht106 HC HF
  ipureintro; rfl

end SetBlockchainInterface

end WNear.Binary.SetBlockchainInterface
