import Bridge.Functions.ValueReturn
import NearLogic.Hosts.LogUtf8

/-!
# `env::log_str` (function 546), through the blockchain interface

```wat
;; 546 log_str(ptr, len)
sp -= 16;  [sp+12] := len;  [sp+8] := ptr   ;; the slice &[u8]
call 452(1055020, sp + 8)                   ;; BLOCKCHAIN_INTERFACE.with(|b| b.log_utf8(..))
sp += 16

;; 452 LocalKey::with(key, &slice): as 456 (ValueReturn.lean), the vtable slot 104 (index 61),
;; the arguments (data, len, ptr) as u64; then Result<(), AccessError>::expect (433) on Ok

;; 263: local.get 1  local.get 2  call 23      ;; the log_utf8 host
```

The installed interface (`Interface.iface`) does not hold the vtable slot of `log_utf8`;
`lslot` is it (`slot n ta 104 61 (A 263)`), and `lCode` holds the trampoline 263 and the host
import 23. The message must be valid UTF-8, fit the remaining log length and count, and its
per-byte read cost a `u64` (`LogOk`).

* `f263_spec`: the trampoline: 3 instructions and `logUtf8Use h len` (`logUtf8_readContract`);
  the host becomes `h` with `bs` logged (`logged h bs`).
* `f452_spec`: `LocalKey::with` on the installed interface: 237 `regular_op_cost`s and the host's
  gas.
* `f546_spec`: `env::log_str(msg)`: 267 and the host's gas.
-/

namespace WNear.Binary.LogStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-! ## The binary's facts -/

/-- `log_utf8`: the vtable's offset 104 holds the table index 61. -/
theorem vtable_logUtf8 : dataWord (1050188 + 104) = bytes32 61 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entry 61: the trampoline 263. -/
theorem wTable_61 : wTable.elems[61]? = some (Ref.func 263) := rfl

/-- Import 23: `log_utf8`. -/
theorem wStore_logUtf8 (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[23]? =
      some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn).toHostFn) := by
  simp [wStore, wHosts]

/-- The host with the message `bs` logged. -/
def logged (h : NearState) (bs : List UInt8) : NearState := { h with logs := h.logs ++ [bs] }

/-- What `log_utf8` needs of the message `bs` of `len` bytes and of the host `h`. -/
structure LogOk (h : NearState) (bs : List UInt8) (k : Nat) : Prop where
  length : bs.length = k
  pos : 0 < k
  utf8 : validUtf8 bs = true
  room : LogRoom h
  fits : LogFits h k
  ov : h.extCosts.cost "read_memory_byte" * k < 2 ^ 64

/-! ## The slot and the code -/

section Inv

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The vtable slot of `log_utf8`. -/
def lslot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 104 61 (A 263)

/-- The code of `log_utf8` past `ifaceCode`: the trampoline 263 and the host 23. -/
def lCode (e inst : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(A 263 ↪[wf] FuncInst.wasm types[4]! inst f263 ∗
    A 23 ↪[wf] FuncInst.host (metered e "log_utf8" logUtf8Fn).toHostFn)

instance (e inst : Nat) (A : Nat → Nat) : Persistent (lCode (GF := GF) e inst A) := by
  unfold lCode; infer_instance

theorem lslot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 104 ] dataWord (1050188 + 104) ∗ ta ↦[wt][ 61 ] Ref.func (A 263) ⊢
      lslot (GF := GF) n ta A := by
  rw [vtable_logUtf8]
  iintro ⟨H, T⟩
  iunfold lslot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

end Inv

/-! ## The trampoline (263) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (len ptr : UInt64) (bs : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 len, .i64 ptr]⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] bs)

def trampPost (n : Nat) (h : NearState) (ptr : UInt64) (bs : List UInt8) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ mhostPt (logged h bs) ∗ n ↦[wms][ ptr.toNat ] bs)

/-- `VmBlockchainInterface::log_utf8` (263, the vtable's index 61): `log_utf8(len, ptr)`
(import 23) of the `len` bytes `bs` at `ptr`. -/
theorem f263_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e n a23 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[23]? = some a23)
    (Cg : Nat) (h : NearState) (dp : UInt32) (len ptr : UInt64) (bs : List UInt8)
    (hlen : len ≠ u64Max) (hok : LogOk h bs len.toNat) :
    a23 ↪[wf] FuncInst.host (metered e "log_utf8" logUtf8Fn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f263 Cg (trampPre n h dp len ptr bs)
        (fun _ => 3 * cfg.regularOpCost + logUtf8Use h len.toNat) (trampPost n h ptr bs) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost, Hb⟩
  subst hargs
  simp only [f263]
  mstep; mstep
  iapply mwpi_call_host_ro' 23 a23 n ptr.toNat _ h (logged h bs) mx bs [.i64 len, .i64 ptr]
    [] ha hn rfl (logUtf8_readContract (C := Cg) e h len ptr bs hlen hok.length hok.pos hok.utf8 hok.room
      hok.fits hok.ov)
  iframe Hc Hh Hm Hhost Hb
  isplitr
  · ipureintro; mstep_norm_full; omega
  inext
  iintro Hhost Hb Hc
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold trampPost
  iframe Hhost Hb
  ipureintro; rfl

end Tramp

/-! ## `LocalKey::with` (452), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key and a pointer to the slice `(ptr, len)`; the stack pointer, the interface, the frame
below `sp`, the bytes and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (bs : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 sl]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ lslot n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] bs ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (bs : List UInt8) (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ lslot n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ ptr.toNat ] bs ∗
    mhostPt (logged h bs))

set_option maxHeartbeats 1000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.log_utf8(slice))` (452) on the installed interface: 237
`regular_op_cost`s and the host's gas. -/
theorem f452_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (sl ptr len : UInt32) (bs : List UInt8)
    (hok : LogOk h bs len.toNat) (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx ∗ lCode e inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f452 Cg
        (withPre n g ta A gi sp sl ptr len bs w0 w4 w8 w12 h)
        (fun _ => 237 * cfg.regularOpCost + logUtf8Use h len.toNat)
        (withPost n g ta A gi sp sl ptr len bs h) := by
  iintro ⟨#Hcode, #HL⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold lCode at HL
  icases HL with ⟨#F263, #H23⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HL, Sp, Sl, HF, Hb, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, S188⟩
  iunfold lslot, slot at HL
  icases HL with ⟨S104, T61⟩
  iunfold frame4 at HF
  icases HF with ⟨W0, W4, W8, W12⟩
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e12 : (sp - 16 + 12).toNat = (sp - 16).toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hor : (sp - 16 + 8) ||| 4 = sp - 16 + 12 := or_four _ (by omega) (by omega)
  have hg := hm.glob
  have hn := hm.mem
  have ha429 := hm.funcs 429 (by decide)
  have ha430 := hm.funcs 430 (by decide)
  have ha431 := hm.funcs 431 (by decide)
  have ha433 := hm.funcs 433 (by decide)
  have t429 : types[31]!.params.length = 3 := by rfl
  have t430 : types[13]!.params.length = 2 := by rfl
  have t431 : types[0]!.params.length = 1 := by rfl
  have t433 : types[0]!.params.length = 1 := by rfl
  have hlen64 : UInt64.ofNat len.toNat ≠ u64Max := by
    have := len.toNat_lt
    intro h'
    have h'' := congrArg UInt64.toNat h'
    simp [u64Max] at h''
    omega
  have hok' : LogOk h bs (UInt64.ofNat len.toNat).toNat := by rw [toNat_ofNat32]; exact hok
  simp only [f452]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mstep; mstep [Hkey]
  -- `__getit` through the table
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 1) (t := 0) (ta := ta) (idx := 116) (a := A 565)
    (type := types[1]!) (inst := inst) (mi := mi) (code := f565) [])
  isplitr
  · iapply (Borrow.f565_spec cfg lim (d + 1) types[1]! (by rfl) inst mi n (A 468) hm.mem
      (hm.funcs 468 (by decide)) types[13]! (by rfl) (by rfl) (by omega) Cg)
    mpersist
  isplitr
  · iexact F565
  isplitr
  · iexact Hi
  isplitl [T116]
  · simp only [UInt32.reduceToNat]; iexact T116
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hst]
  · iunfold Borrow.getItPre
    iframe Hst
    ipureintro; rfl
  inext
  iintro %rs T116 Hc HQ
  iunfold Borrow.getItPost at HQ
  icases HQ with ⟨%hrs, Hst⟩
  subst hrs
  mctrl_norm
  -- not null
  mstep; mstep; mstep
  -- `RefCell::borrow`
  mstep; mstep; mstep
  mcall (Borrow.f429_spec cfg lim (d + 1) types[31]! (by rfl) inst mi n g (A 494) (A 672) hm.mem
      hm.glob (hm.funcs 494 (by decide)) (hm.funcs 672 (by decide)) types[32]! types[13]! (by rfl)
      (by rfl) (by rfl) (by rfl) (by omega) Cg { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl
      (sp - 16) 1074904 1056228 w0 w4 (by decide)) using [Hg Hfl W0 W4]
  · iunfold Borrow.borrowPre
    simp only [UInt32.reduceToNat]
    iframe Hg Hfl W0 W4
  iunfold Borrow.borrowPost at HQ
  icases HQ with ⟨%hrs, Hg, Hfl, W0, W4⟩
  subst hrs
  simp only [UInt32.reduceToNat, UInt32.reduceAdd]
  -- the `Ref` copied
  mstep; mstep; mstep [W4]; mstep [W12]
  mstep; mstep; mstep [W0]; mstep; mstep [W8]
  mstep; mstep
  -- `Some`: the box
  try simp only [UInt32.reduceOfNat]
  mstep; mstep
  try simp only [UInt32.reduceOfNat]
  mstep
  mstep [Hda]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply Borrow.mwpi_select_true'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; exact ⟨by mstep_norm_full; omega, by decide⟩
  inext
  iintro Hc
  mctrl_norm
  mstep
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1056244
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `log_utf8`
  mstep; mstep [Hda]; mstep; mstep [Sl]; mstep; mstep [Sp]
  simp only [load32u, UInt32.reduceOfNat]
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S104]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 4) (t := 0) (ta := ta) (idx := 61) (a := A 263)
    (type := types[4]!) (inst := inst) (mi := mi) (code := f263)
    [.i32 1, .i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat)])
  isplitr
  · iapply (f263_spec cfg lim (d + 1) types[4]! (by rfl) inst mi e n (A 23) mx hm.mem
      (hm.funcs 23 (by decide)) Cg h 1 (UInt64.ofNat len.toNat) (UInt64.ofNat ptr.toNat) bs hlen64 hok')
    mpersist
  isplitr
  · iexact F263
  isplitr
  · iexact Hi
  isplitl [T61]
  · simp only [UInt32.reduceToNat]; iexact T61
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; simp only [toNat_ofNat32]; mstep_norm_full; omega
  isplitl [Hhost Hb]
  · iunfold trampPre
    rw [toNat_ofNat32]
    iframe Hhost Hb
    ipureintro; rfl
  inext
  iintro %rs T61 Hc HQ
  iunfold trampPost at HQ
  icases HQ with ⟨%hrs, Hhost, Hb⟩
  subst hrs
  rw [toNat_ofNat32]
  mctrl_norm
  -- the `Ref` dropped
  mstep; mstep; mstep; mstep; mstep
  rw [hor]
  mcall (Borrow.f431_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n (A 672) hm.mem
      (hm.funcs 672 (by decide)) types[13]! (by rfl) (by rfl) (by omega) Cg (sp - 16 + 12) 1074904 1)
    using [W12 Hfl]
  · iunfold Borrow.dropPre
    rw [e12]
    simp only [UInt32.reduceToNat]
    iframe W12 Hfl
  iunfold Borrow.dropPost at HQ
  icases HQ with ⟨%hrs, W12, Hfl⟩
  subst hrs
  rw [e12]
  simp only [UInt32.reduceToNat, UInt32.reduceAdd]
  mstep
  -- `Result::expect`
  mstep
  mcall (BorrowMut.f433_spec cfg lim (d + 1) types[0]! (by rfl) inst mi g hm.glob Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl) using [Hg]
  · iunfold BorrowMut.expectPre
    iframe Hg
    ipureintro; rfl
  iunfold BorrowMut.expectPost at HQ
  icases HQ with ⟨%hrs, Hg⟩
  subst hrs
  -- sp += 16
  mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e]
  rw [toNat_ofNat32]
  mcredits R
  iframe Hc
  iunfold withPost, iface, lslot, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 S104 T61 Sp Sl W0 W4 W8 W12 Hb Hhost

end With

/-! ## `env::log_str` (546) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The message's pointer and length; the stack pointer, the interface, the two words of 546's
frame (at `sp - 8`), `LocalKey::with`'s frame (at `sp - 32`), the bytes and the host. -/
def pre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp ptr len : UInt32) (bs : List UInt8)
    (s8 s12 w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 ptr, .i32 len]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ lslot n ta A ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] s8 ∗ n ↦[i32][ (sp - 16).toNat + 12 ] s12 ∗
    frame4 n (sp - 16 - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] bs ∗ mhostPt h)

/-- The message logged; the interface back. -/
def post (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp ptr len : UInt32) (bs : List UInt8)
    (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ lslot n ta A ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] ptr ∗ n ↦[i32][ (sp - 16).toNat + 12 ] len ∗
    frame4 n (sp - 16 - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ ptr.toNat ] bs ∗
    mhostPt (logged h bs))

/-- **`env::log_str(msg)`** (function 546 of `contract.wasm`) on the installed blockchain
interface, the `len` bytes `bs` at `ptr` (`LogOk`): the message logged; 267 `regular_op_cost`s and
`logUtf8Use h len`. -/
theorem f546_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 32 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (ptr len : UInt32) (bs : List UInt8)
    (hok : LogOk h bs len.toNat) (s8 s12 w0 w4 w8 w12 : UInt32) :
    A 452 ↪[wf] FuncInst.wasm types[14]! inst f452 ∗ ifaceCode e inst mi A n mx ∗ lCode e inst A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f546 Cg
        (pre n g ta A gi sp ptr len bs s8 s12 w0 w4 w8 w12 h)
        (fun _ => 267 * cfg.regularOpCost + logUtf8Use h len.toNat)
        (post n g ta A gi sp ptr len bs h) := by
  iintro ⟨#F452, #Hcode, #HL⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  ihave #HCL : (ifaceCode (GF := GF) e inst mi A n mx ∗ lCode e inst A) $$ []
  · isplitr
    · iexact Hcode
    · iexact HL
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, HI, HLs, S8, S12, HF, Hb, Hhost⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have hg := hm.glob
  have hn := hm.mem
  have ha452 := hm.funcs 452 (by decide)
  have t452 : types[14]!.params.length = 2 := by rfl
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  simp only [f546]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [S12]
  mstep; mstep; mstep [S8]
  mstep; mstep; mstep; mstep
  ihave S12 := (memBytes_congr (j := (sp - 16).toNat + 8 + 4) (by omega)).1 $$ S12
  mcall (f452_spec cfg lim (d + 1) types[14]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl (by omega) (by omega) h (sp - 16 + 8)
      ptr len bs hok w0 w4 w8 w12) using [Hg HI HLs S8 S12 HF Hb Hhost]
  · iunfold withPre
    rw [e8]
    iframe Hg HI HLs S8 S12 HF Hb Hhost
    ipureintro; rfl
  iunfold withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, HLs, S8, S12, HF, Hb, Hhost⟩
  subst hrs
  rw [e8]
  ihave S12 := (memBytes_congr (j := (sp - 16).toNat + 12) (by omega)).1 $$ S12
  mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e]
  mcredits R
  iframe Hc
  iunfold post
  iframe Hg HI HLs S8 S12 HF Hb Hhost
  ipureintro; rfl

end Spec

end WNear.Binary.LogStr
