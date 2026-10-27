import Bridge.Functions.RegisterLen
import NearLogic.Hosts.ValueReturn

/-!
# `env::value_return` (function 545), through the blockchain interface

```wat
;; 545 value_return(ptr, len)
sp -= 16;  [sp+12] := len;  [sp+8] := ptr   ;; the slice &[u8]
call 456(1055020, sp + 8)                   ;; BLOCKCHAIN_INTERFACE.with(|b| b.value_return(..))
sp += 16

;; 456 LocalKey::with(key, &slice): as 440 (RegisterLen.lean), the vtable
;; slot 92 (index 58), the arguments (data, len, ptr) as u64; then
;; Result<(), AccessError>::expect (433) on Ok

;; 260: local.get 1  local.get 2  call 20      ;; the value_return host
```

* `f260_spec`: the trampoline: 3 instructions and `valueReturnUse h len`
  (`valueReturn_readContract`); the host becomes `h.selectReturnValue bs`.
* `f456_spec`: `LocalKey::with` on the installed interface: 237
  `regular_op_cost`s and the host's gas.
* `f545_spec`: `env::value_return(ptr, len)`: 267 and the host's gas.
-/

namespace WNear.Binary.ValueReturn

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

theorem load32u (x : Nat) :
    loadValue .i64 (some { bits := 32, signed := false }) x = .i64 (UInt64.ofNat x) := by
  simp [loadValue]

theorem load32u_bytes32 (w : UInt32) :
    loadValue .i64 (some { bits := 32, signed := false }) (Memory.decodeLE (bytes32 w)) =
      .i64 (UInt64.ofNat w.toNat) := by
  simp [loadValue, decodeLE_bytes32]

theorem toNat_ofNat32 (w : UInt32) : (UInt64.ofNat w.toNat).toNat = w.toNat := by
  have := w.toNat_lt
  simp

/-! ## The trampoline (260) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (len ptr : UInt64) (bs : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 len, .i64 ptr]⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] bs)

def trampPost (n : Nat) (h : NearState) (ptr : UInt64) (bs : List UInt8) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ mhostPt (h.selectReturnValue bs) ∗ n ↦[wms][ ptr.toNat ] bs)

/-- `VmBlockchainInterface::value_return` (260, the vtable's index 58):
`value_return(len, ptr)` (import 20) of the `len` bytes `bs` at `ptr`. -/
theorem f260_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e n a20 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[20]? = some a20)
    (Cg : Nat) (h : NearState) (dp : UInt32) (len ptr : UInt64) (bs : List UInt8)
    (hlen : len ≠ u64Max) (hbs : bs.length = len.toNat)
    (hlim : withinLimit h.config.maxReturnLen len.toNat = true) (hpos : 0 < len.toNat) :
    a20 ↪[wf] FuncInst.host (metered e "value_return" valueReturnFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f260 Cg (trampPre n h dp len ptr bs)
        (fun _ => 3 * cfg.regularOpCost + valueReturnUse h len.toNat) (trampPost n h ptr bs) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost, Hb⟩
  subst hargs
  simp only [f260]
  mstep; mstep
  iapply mwpi_call_host_ro' 20 a20 n ptr.toNat _ h (h.selectReturnValue bs) mx bs [.i64 len, .i64 ptr]
    [] ha hn rfl (valueReturn_readContract (C := Cg) e h len ptr bs hlen hbs hlim hpos)
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

/-! ## `LocalKey::with` (456), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key and a pointer to the slice `(ptr, len)`; the stack pointer, the
interface, the frame below `sp`, the bytes and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (bs : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 sl]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] bs ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp sl ptr len : UInt32)
    (bs : List UInt8) (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[i32][ sl.toNat ] ptr ∗ n ↦[i32][ sl.toNat + 4 ] len ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ ptr.toNat ] bs ∗
    mhostPt (h.selectReturnValue bs))

set_option maxHeartbeats 1000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.value_return(slice))` (456) on the
installed interface: 237 `regular_op_cost`s and the host's gas. -/
theorem f456_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (sl ptr len : UInt32) (bs : List UInt8)
    (hbs : bs.length = len.toNat)
    (hlim : withinLimit h.config.maxReturnLen len.toNat = true) (hpos : 0 < len.toNat)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCode e inst mi A n mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f456 Cg
        (withPre n g ta A gi sp sl ptr len bs w0 w4 w8 w12 h)
        (fun _ => 237 * cfg.regularOpCost + valueReturnUse h len.toNat)
        (withPost n g ta A gi sp sl ptr len bs h) := by
  iintro #Hcode
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, Sp, Sl, HF, Hb, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, ⟨S92, T58⟩, S188⟩
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
  simp only [f456]
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
      (sp - 16) 1074904 1056148 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1056164
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `value_return`
  mstep; mstep [Hda]; mstep; mstep [Sl]; mstep; mstep [Sp]
  simp only [load32u, UInt32.reduceOfNat]
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S92]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 4) (t := 0) (ta := ta) (idx := 58) (a := A 260)
    (type := types[4]!) (inst := inst) (mi := mi) (code := f260)
    [.i32 1, .i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat)])
  isplitr
  · iapply (f260_spec cfg lim (d + 1) types[4]! (by rfl) inst mi e n (A 20) mx hm.mem
      (hm.funcs 20 (by decide)) Cg h 1 (UInt64.ofNat len.toNat) (UInt64.ofNat ptr.toNat) bs hlen64
      (by rw [toNat_ofNat32]; exact hbs) (by rw [toNat_ofNat32]; exact hlim)
      (by rw [toNat_ofNat32]; exact hpos))
    mpersist
  isplitr
  · iexact F260
  isplitr
  · iexact Hi
  isplitl [T58]
  · simp only [UInt32.reduceToNat]; iexact T58
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
  iintro %rs T58 Hc HQ
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
  iunfold withPost, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 T58 S188 Sp Sl W0 W4 W8 W12 Hb Hhost

end With

/-! ## `env::value_return` (545) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The bytes' pointer and length; the stack pointer, the interface, the two
words of 545's frame (at `sp - 8`), `LocalKey::with`'s frame (at `sp - 32`),
the bytes and the host. -/
def pre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp ptr len : UInt32) (bs : List UInt8)
    (s8 s12 w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 ptr, .i32 len]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] s8 ∗ n ↦[i32][ (sp - 16).toNat + 12 ] s12 ∗
    frame4 n (sp - 16 - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] bs ∗ mhostPt h)

/-- The return value selected: the host `h.selectReturnValue bs`; the
interface back. -/
def post (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp ptr len : UInt32) (bs : List UInt8)
    (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] ptr ∗ n ↦[i32][ (sp - 16).toNat + 12 ] len ∗
    frame4 n (sp - 16 - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ ptr.toNat ] bs ∗
    mhostPt (h.selectReturnValue bs))

/-- **`env::value_return(bytes)`** (function 545 of `contract.wasm`) on the
installed blockchain interface, the `len` (nonzero, within the limit) bytes
`bs` at `ptr`: 267 `regular_op_cost`s and `valueReturnUse h len`. -/
theorem f545_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 32 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (ptr len : UInt32) (bs : List UInt8)
    (hbs : bs.length = len.toNat) (hlim : withinLimit h.config.maxReturnLen len.toNat = true)
    (hpos : 0 < len.toNat) (s8 s12 w0 w4 w8 w12 : UInt32) :
    A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗ ifaceCode e inst mi A n mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f545 Cg
        (pre n g ta A gi sp ptr len bs s8 s12 w0 w4 w8 w12 h)
        (fun _ => 267 * cfg.regularOpCost + valueReturnUse h len.toNat)
        (post n g ta A gi sp ptr len bs h) := by
  iintro ⟨#F456, #Hcode⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, HI, S8, S12, HF, Hb, Hhost⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have hg := hm.glob
  have hn := hm.mem
  have ha456 := hm.funcs 456 (by decide)
  have t456 : types[14]!.params.length = 2 := by rfl
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  simp only [f545]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [S12]
  mstep; mstep; mstep [S8]
  mstep; mstep; mstep; mstep
  ihave S12 := (memBytes_congr (j := (sp - 16).toNat + 8 + 4) (by omega)).1 $$ S12
  mcall (f456_spec cfg lim (d + 1) types[14]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl (by omega) (by omega) h (sp - 16 + 8)
      ptr len bs hbs hlim hpos w0 w4 w8 w12) using [Hg HI S8 S12 HF Hb Hhost]
  · iunfold withPre
    rw [e8]
    iframe Hg HI S8 S12 HF Hb Hhost
    ipureintro; rfl
  iunfold withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, S8, S12, HF, Hb, Hhost⟩
  subst hrs
  rw [e8]
  ihave S12 := (memBytes_congr (j := (sp - 16).toNat + 12) (by omega)).1 $$ S12
  mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e]
  mcredits R
  iframe Hc
  iunfold post
  iframe Hg HI S8 S12 HF Hb Hhost
  ipureintro; rfl

end Spec

end WNear.Binary.ValueReturn
