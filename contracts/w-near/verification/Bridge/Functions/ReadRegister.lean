import Bridge.Functions.ValueReturn
import Bridge.Functions.VecFromElem
import Bridge.Functions.VecDeref
import Binary.Code.Part13

/-!
# `env::read_register` (function 523), through the blockchain interface

```wat
;; 523 read_register(out, id) -> Option<Vec<u8>> at out
sp -= 48;  [sp+24] := id (i64)
register_len(sp + 8, id)                       ;; 524: Option<u64> at sp+8
if [sp+8] = None:  out.ptr := 0                ;; None (762 is a no-op)
else:
  from_elem(sp + 32, 0, len as u32)             ;; 687: vec![0u8; len]
  435(1055020, sp + 24, sp + 32)               ;; BLOCKCHAIN_INTERFACE.with(|b| b.read_register(id, vec.ptr))
  out := (vec.ptr, vec.cap, vec.len)
sp += 48

;; 435 LocalKey::with(key, &id, &vec): as 456 (ValueReturn.lean), the vtable slot 12
;; (table index 38), the arguments (data, id, vec.ptr as u64)
;; 240: local.get 1  local.get 2  call 0       ;; the read_register host
```

The installed interface (`Interface.iface`) does not hold the vtable slot of
`read_register`; `ifaceR` is it with that slot (`slot n ta 12 38 (A 240)`), and
`ifaceCodeR` adds the trampoline 240 and the host import 0 to `ifaceCode`.
`ifaceR_of_iface` builds `ifaceR` from `iface`, the vtable word (data segment) and the
table entry; `wTable_38`, `wStore_readRegister` are the binary's facts.

* `f240_spec`: the trampoline: `read_register(r, ptr)` under `readRegister_rwContract`
  (the register holds `data`, nonempty), 3 `regular_op_cost`s and `readRegisterUse h len`.
* `f435_spec`: `LocalKey::with` on the installed interface: 237 and the host's gas.
* `f523_spec`: `env::read_register(id)`: `None` (the register unset) or `Some(vec)`
  with `vec = data`, the heap updated (`regVec`).
-/

namespace WNear.Binary.ReadRegister

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface WNear.Binary.RegisterLen WNear.Binary.ValueReturn
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-! ## The binary's facts -/

/-- `read_register`: the vtable's offset 12 holds the table index 38. -/
theorem vtable_readRegister : dataWord (1050188 + 12) = bytes32 38 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entry 38: the trampoline 240. -/
theorem wTable_38 : wTable.elems[38]? = some (Ref.func 240) := rfl

/-- Import 0: `read_register`. -/
theorem wStore_readRegister (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[0]? =
      some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "read_register" readRegisterFn).toHostFn) := by
  simp [wStore, wHosts]

/-! ## The interface with `read_register` -/

section Inv

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The installed interface and the vtable slot of `read_register`. -/
def ifaceR (n ta : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(iface n ta A ∗ slot n ta 12 38 (A 240))

/-- `ifaceCode` and the code of `read_register`: the trampoline 240 and the host 0. -/
def ifaceCodeR (e : Nat) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    IProp GF :=
  iprop(ifaceCode e inst mi A n mx ∗ A 240 ↪[wf] FuncInst.wasm types[4]! inst f240 ∗
    A 0 ↪[wf] FuncInst.host (metered e "read_register" readRegisterFn).toHostFn)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (ifaceCodeR (GF := GF) e inst mi A n mx) := by
  unfold ifaceCodeR; infer_instance

theorem ifaceR_of_iface (n ta : Nat) (A : Nat → Nat) :
    iface n ta A ∗ n ↦[wms][ 1050188 + 12 ] dataWord (1050188 + 12) ∗ ta ↦[wt][ 38 ] Ref.func (A 240)
      ⊢ ifaceR (GF := GF) n ta A := by
  rw [vtable_readRegister]
  iintro ⟨HI, H, T⟩
  iunfold ifaceR, slot
  simp only [UInt32.reduceToNat]
  iframe HI H T

theorem iface_of_ifaceR (n ta : Nat) (A : Nat → Nat) :
    ifaceR (GF := GF) n ta A ⊢ iface n ta A ∗ slot n ta 12 38 (A 240) := by
  iintro H; iunfold ifaceR at H; iexact H

end Inv

/-! ## The trampoline (240) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}
  {Cg K : Nat}

/-- `mwpi_call_host_rw` on a stack holding just the arguments, any credits covering it. -/
theorem mwpi_call_host_rw' (i a n ptr : Nat) (fn : HostFn NearState) (h h' : NearState) (mx : Option Nat)
    (old new : List UInt8) (args rs : List Value) {kh : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length) (hl : new.length = old.length)
    (hc : RWContract fn h h' args rs ptr old new kh Cg) :
    credits Cg K ∗ ⌜cfg.regularOpCost + kh ≤ K⌝ ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗
      mhostPt h ∗ n ↦[wms][ ptr ] old ∗
      ▷ (mhostPt h' -∗ n ↦[wms][ ptr ] new -∗ credits Cg (K - (cfg.regularOpCost + kh)) -∗
        Φ.normal rs f)
      ⊢ mwpi cfg lim d f args [.call i] Φ := by
  iintro ⟨Hc, %hK, Hf, Hm, Hh, Hb, H⟩
  have r := mwpi_call_host_rw (cfg := cfg) (lim := lim) (d := d) (f := f) (Φ := Φ)
    (R := K - (cfg.regularOpCost + kh)) i a n ptr fn h h' mx old new [] args rs ha hn hlen hl hc
  simp only [List.nil_append] at r
  iapply r
  rw [show cfg.regularOpCost + kh + (K - (cfg.regularOpCost + kh)) = K by omega]
  iframe Hc Hf Hm Hh Hb H

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (r ptr : UInt64) (old : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 r, .i64 ptr]⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] old)

def trampPost (n : Nat) (h : NearState) (ptr : UInt64) (data : List UInt8) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ mhostPt h ∗ n ↦[wms][ ptr.toNat ] data)

/-- `VmBlockchainInterface::read_register` (240, the vtable's index 38): `read_register(r, ptr)`
(import 0), the register `r` holding the nonempty `data`, written over the `old` bytes. -/
theorem f240_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e n a0 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[0]? = some a0)
    (Cg : Nat) (h : NearState) (dp : UInt32) (r ptr : UInt64) (old data : List UInt8)
    (hreg : h.registers r.toNat = some data) (hold : old.length = data.length) (hpos : 0 < data.length) :
    a0 ↪[wf] FuncInst.host (metered e "read_register" readRegisterFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f240 Cg (trampPre n h dp r ptr old)
        (fun _ => 3 * cfg.regularOpCost + readRegisterUse h data.length) (trampPost n h ptr data) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost, Hb⟩
  subst hargs
  simp only [f240]
  mstep; mstep
  iapply mwpi_call_host_rw' 0 a0 n ptr.toNat _ h h mx old data [.i64 r, .i64 ptr] [] ha hn rfl hold.symm
    (readRegister_rwContract (C := Cg) e h r ptr data old hreg hold hpos)
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

/-! ## `LocalKey::with` (435), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key, a pointer to the register id and one to the `Vec` (its pointer word); the stack
pointer, the interface, the frame below `sp`, the `Vec`'s bytes and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp idp vp ptr : UInt32) (r : UInt64)
    (old : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 idp, .i32 vp]⌝ ∗ g ↦[wg] gi ∗ ifaceR n ta A ∗
    n ↦[wms][ idp.toNat ] storeBytes (.i64 r) 8 ∗ n ↦[i32][ vp.toNat ] ptr ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] old ∗ mhostPt h)

def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp idp vp ptr : UInt32) (r : UInt64)
    (data : List UInt8) (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ ifaceR n ta A ∗
    n ↦[wms][ idp.toNat ] storeBytes (.i64 r) 8 ∗ n ↦[i32][ vp.toNat ] ptr ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ n ↦[wms][ ptr.toNat ] data ∗ mhostPt h)

set_option maxHeartbeats 1000000 in
/-- `BLOCKCHAIN_INTERFACE.with(|b| b.read_register(id, vec.ptr))` (435) on the installed
interface, the register holding the nonempty `data`: 237 `regular_op_cost`s and the host's
gas. -/
theorem f435_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (h : NearState) (idp vp ptr : UInt32) (r : UInt64) (old data : List UInt8)
    (hreg : h.registers r.toNat = some data) (hold : old.length = data.length) (hdpos : 0 < data.length)
    (w0 w4 w8 w12 : UInt32) :
    ifaceCodeR e inst mi A n mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f435 Cg
        (withPre n g ta A gi sp idp vp ptr r old w0 w4 w8 w12 h)
        (fun _ => 237 * cfg.regularOpCost + readRegisterUse h data.length)
        (withPost n g ta A gi sp idp vp ptr r data h) := by
  iintro #HcodeR
  iunfold ifaceCodeR, ifaceCode at HcodeR
  icases HcodeR with ⟨⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩, #F240, #H0⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, Hid, Hvp, HF, Hb, Hhost⟩
  subst hargs
  iunfold ifaceR, iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, S16, S92, S188⟩, ⟨S12, T38⟩⟩
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
  simp only [f435]
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
      (sp - 16) 1074904 1055160 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1055208
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `value_return`
  mstep; mstep [Hda]; mstep; mstep [Hid] with simp [storeBytes]
  simp only [decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep [Hvp]
  simp only [load32u_bytes32, UInt32.reduceOfNat]
  mstep; mstep [Hvt]
  try simp only [UInt32.reduceOfNat]
  mstep [S12]
  try simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 4) (t := 0) (ta := ta) (idx := 38) (a := A 240)
    (type := types[4]!) (inst := inst) (mi := mi) (code := f240)
    [.i32 1, .i64 r, .i64 (UInt64.ofNat ptr.toNat)])
  isplitr
  · iapply (f240_spec cfg lim (d + 1) types[4]! (by rfl) inst mi e n (A 0) mx hm.mem
      (hm.funcs 0 (by decide)) Cg h 1 r (UInt64.ofNat ptr.toNat) old data hreg hold hdpos)
    mpersist
  isplitr
  · iexact F240
  isplitr
  · iexact Hi
  isplitl [T38]
  · simp only [UInt32.reduceToNat]; iexact T38
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hhost Hb]
  · iunfold trampPre
    try rw [toNat_ofNat32]
    iframe Hhost Hb
    ipureintro; rfl
  inext
  iintro %rs T38 Hc HQ
  iunfold trampPost at HQ
  icases HQ with ⟨%hrs, Hhost, Hb⟩
  subst hrs
  try rw [toNat_ofNat32]
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
  try rw [toNat_ofNat32]
  mcredits R
  iframe Hc
  iunfold withPost, ifaceR, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe Hg Hkey T116 Hst Hfl Hda Hvt S16 S92 S188 S12 T38 Hid Hvp W0 W4 W8 W12 Hb Hhost


end With

/-! ## Stack words -/

section Words

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk16 stk16_join)
open WNear.Binary.AllocNewCell (memBytes_addr)

theorem bytes32_of (bs : List UInt8) (h : bs.length = 4) : bs = bytes32 (UInt32.ofNat (Memory.decodeLE bs)) := by
  have := VecDeref.storeBytes_load_i32 bs h
  rw [← storeBytes_i32]
  simpa [loadValue] using this.symm

theorem stk4_word (n a : Nat) : stk (GF := GF) n a 4 ⊢ ∃ w : UInt32, n ↦[i32][ a ] w := by
  iintro H
  iunfold stk at H
  icases H with ⟨%bs, %hbs, H⟩
  iexists UInt32.ofNat (Memory.decodeLE bs)
  rw [← bytes32_of bs hbs]
  iexact H

theorem stk_frame4 (n a : Nat) (fp : UInt32) (h : fp.toNat = a) :
    stk (GF := GF) n a 16 ⊢ ∃ w0 w4 w8 w12 : UInt32, frame4 n fp w0 w4 w8 w12 := by
  iintro H
  icases stk16 n a $$ H with ⟨H0, H4, H8, H12⟩
  icases stk4_word n _ $$ H0 with ⟨%w0, H0⟩
  icases stk4_word n _ $$ H4 with ⟨%w4, H4⟩
  icases stk4_word n _ $$ H8 with ⟨%w8, H8⟩
  icases stk4_word n _ $$ H12 with ⟨%w12, H12⟩
  iexists w0, w4, w8, w12
  iunfold frame4
  subst h
  iframe H0 H4 H8 H12

theorem frame4_stk (n a : Nat) (fp : UInt32) (h : fp.toNat = a) (w0 w4 w8 w12 : UInt32) :
    frame4 (GF := GF) n fp w0 w4 w8 w12 ⊢ stk n a 16 := by
  iintro H
  iunfold frame4 at H
  icases H with ⟨H0, H4, H8, H12⟩
  iapply stk16_join
  subst h
  ihave H0 := stk_word n _ w0 $$ H0
  ihave H4 := stk_word n _ w4 $$ H4
  ihave H8 := stk_word n _ w8 $$ H8
  ihave H12 := stk_word n _ w12 $$ H12
  iframe H0 H4 H8 H12

theorem stk_bytes (n a : Nat) (bs : List UInt8) (k : Nat) (h : bs.length = k) :
    n ↦[wms][ a ] bs ⊢ stk (GF := GF) n a k := by
  iintro H; iunfold stk; iexists bs; iframe H; ipureintro; exact h

theorem wrap_ofNat (L : Nat) : (UInt64.ofNat L).toUInt32 = UInt32.ofNat L := by
  apply UInt32.toNat_inj.mp; simp

theorem tag_some (L : Nat) (h : L < 2 ^ 32) : optTag (UInt64.ofNat L) = 1 := by
  unfold optTag
  rw [if_neg]
  intro e
  have := congrArg UInt64.toNat e
  simp [u64Max] at this
  omega

theorem lenU64_some {h : NearState} {r : UInt64} {data : List UInt8} (hr : h.registers r.toNat = some data) :
    registerLenU64 h r = UInt64.ofNat data.length := by
  unfold registerLenU64; rw [hr]

theorem lenU64_none {h : NearState} {r : UInt64} (hr : h.registers r.toNat = none) :
    registerLenU64 h r = u64Max := by
  unfold registerLenU64; rw [hr]

end Words

section Stack

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.VecFromElem (stk stk_split stk_join vecAfter grownLen)
open WNear.Binary.AllocInv (heapInv)

theorem stk160_join (n S : Nat) (hS : 160 ≤ S) :
    stk (GF := GF) n (S - 160) 80 ∗ stk n (S - 80) 16 ∗ stk n (S - 64) 8 ∗ stk n (S - 56) 8 ∗
      stk n (S - 48) 8 ∗ stk n (S - 40) 8 ∗ stk n (S - 32) 8 ∗ stk n (S - 24) 8 ∗ stk n (S - 16) 16
      ⊢ stk n (S - 160) 160 := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9⟩
  ihave H8 := stk_join n (S - 24) 8 16 $$ [H8 H9]
  · rw [show S - 24 + 8 = S - 16 by omega]; iframe H8 H9
  ihave H7 := stk_join n (S - 32) 8 24 $$ [H7 H8]
  · rw [show S - 32 + 8 = S - 24 by omega]; iframe H7 H8
  ihave H6 := stk_join n (S - 40) 8 32 $$ [H6 H7]
  · rw [show S - 40 + 8 = S - 32 by omega]; iframe H6 H7
  ihave H5 := stk_join n (S - 48) 8 40 $$ [H5 H6]
  · rw [show S - 48 + 8 = S - 40 by omega]; iframe H5 H6
  ihave H4 := stk_join n (S - 56) 8 48 $$ [H4 H5]
  · rw [show S - 56 + 8 = S - 48 by omega]; iframe H4 H5
  ihave H3 := stk_join n (S - 64) 8 56 $$ [H3 H4]
  · rw [show S - 64 + 8 = S - 56 by omega]; iframe H3 H4
  ihave H2 := stk_join n (S - 80) 16 64 $$ [H2 H3]
  · rw [show S - 80 + 16 = S - 64 by omega]; iframe H2 H3
  iapply stk_join n (S - 160) 80 80
  rw [show S - 160 + 80 = S - 80 by omega]
  iframe H1 H2

theorem stk112_join' (n S : Nat) (hS : 160 ≤ S) :
    stk (GF := GF) n (S - 160) 80 ∗ stk n (S - 80) 16 ∗ stk n (S - 64) 8 ∗ stk n (S - 56) 8
      ⊢ stk n (S - 160) 112 := by
  iintro ⟨H1, H2, H3, H4⟩
  ihave H3 := stk_join n (S - 64) 8 8 $$ [H3 H4]
  · rw [show S - 64 + 8 = S - 56 by omega]; iframe H3 H4
  ihave H2 := stk_join n (S - 80) 16 16 $$ [H2 H3]
  · rw [show S - 80 + 16 = S - 64 by omega]; iframe H2 H3
  iapply stk_join n (S - 160) 80 32
  rw [show S - 160 + 80 = S - 80 by omega]
  iframe H1 H2

theorem vecAfter_pos {n maxP len : Nat} {live : List (Nat × Nat)} {c p : UInt32} {b : UInt8}
    (hc : 0 < c.toNat) :
    vecAfter (GF := GF) n maxP len live c p b ⊢
      ∃ len', ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len c)⌝ ∗
        heapInv n maxP len' ((p.toNat, c.toNat) :: live) 1 ∗ n ↦[wms][ p.toNat ] List.replicate c.toNat b := by
  iintro H
  iunfold vecAfter at H
  icases H with ⟨%len', %h, H1, H2⟩
  have hc0 : c.toNat ≠ 0 := by omega
  simp only [hc0, ite_false]
  iexists len'
  iframe H1 H2
  ipureintro
  rcases h with ⟨h0, -, -⟩ | ⟨-, hp, hl⟩
  · omega
  · exact ⟨hp, hl⟩

end Stack


/-! ## `env::read_register` (523) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr vecCode vecAfter roomFor grownLen
  cost687 pre687 post687 f687_spec)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)

/-- `fn () {}` (761, a no-op on the `None` path): no instruction. -/
theorem f761_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (Cg : Nat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f761 Cg (fun args => iprop(⌜args = []⌝))
        (fun _ => 0) (fun _ rs => iprop(⌜rs = []⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  try simp only [f761]
  mstep
  mcredits R
  iframe Hc

/-- The code `read_register` runs (persistent). -/
def rrCode (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(ifaceCodeR e inst mi A n mx ∗ vecCode n maxP inst mi A ∗
    A 524 ↪[wf] FuncInst.wasm types[5]! inst f524 ∗ A 440 ↪[wf] FuncInst.wasm types[30]! inst f440 ∗
    A 435 ↪[wf] FuncInst.wasm types[31]! inst f435 ∗ A 761 ↪[wf] FuncInst.wasm types[21]! inst f761)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (rrCode (GF := GF) e inst mi A n maxP mx) := by
  unfold rrCode; infer_instance

/-- `Option<Vec<u8>>` at `out` for the register's contents: `None` (pointer word 0, the heap
unchanged), or `Some(vec)`, `vec = (p, len, len)`, `p ↦ data` a fresh live block. -/
def optVecAt (n maxP len : Nat) (live : List (Nat × Nat)) (out : UInt32) : Option (List UInt8) → IProp GF
  | none => iprop(n ↦[i32][ out.toNat ] 0 ∗ (∃ bs : List UInt8, ⌜bs.length = 8⌝ ∗ n ↦[wms][ out.toNat + 4 ] bs) ∗
      heapInv n maxP len live 1)
  | some data => iprop(∃ p : UInt32, n ↦[i32][ out.toNat ] p ∗
      n ↦[i32][ out.toNat + 4 ] UInt32.ofNat data.length ∗ n ↦[i32][ out.toNat + 8 ] UInt32.ofNat data.length ∗
      ∃ len', ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len (UInt32.ofNat data.length))⌝ ∗
        heapInv n maxP len' ((p.toNat, data.length) :: live) 1 ∗ n ↦[wms][ p.toNat ] data)

/-- What a register needs for `read_register`: nonempty, `< 2^28` bytes, and room for it. -/
def RegOk (maxP len : Nat) : Option (List UInt8) → Prop
  | none => True
  | some data => 0 < data.length ∧ data.length < 2 ^ 28 ∧ roomFor len maxP (UInt32.ofNat data.length)

/-- The cost of `read_register` past `register_len`. -/
def costRest (cfg : WasmConfig) (h : NearState) : Option (List UInt8) → Nat
    | none => 50 * cfg.regularOpCost
    | some data => 95 * cfg.regularOpCost + cost687 cfg 0 (UInt32.ofNat data.length) +
        (237 * cfg.regularOpCost + readRegisterUse h data.length)

/-- The cost of `read_register`. -/
def cost523 (cfg : WasmConfig) (h : NearState) (r : UInt64) : Nat :=
  281 * cfg.regularOpCost + registerLenUse h + costRest cfg h (h.registers r.toNat)

theorem costRest_ge (cfg : WasmConfig) (h : NearState) (v : Option (List UInt8)) :
    40 * cfg.regularOpCost ≤ costRest cfg h v := by
  cases v <;> simp only [costRest] <;> omega

def pre523 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (r : UInt64) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (ob : List UInt8) (h : NearState) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i64 r]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 160) 160 ∗
    vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1 ∗ n ↦[wms][ out.toNat ] ob ∗ mhostPt h)

def post523 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (r : UInt64) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 160) 160 ∗
    vt n 1057464 idx ta (A 578) ∗ optVecAt n maxP len live out (h.registers r.toNat) ∗ mhostPt h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`env::read_register(id)`** (function 523 of `contract.wasm`) on the installed interface
(with `read_register`'s slot): `None` if the register is unset, else `Some(vec)` with the
register's bytes in a fresh heap block (`optVecAt`). -/
theorem f523_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 160 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (r : UInt64) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (hok : RegOk maxP len (h.registers r.toNat)) :
    rrCode e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f523 Cg
        (pre523 n g ta A gt s out r idx maxP len live ob h)
        (fun _ => cost523 cfg h r)
        (post523 n g ta A gt s out r idx maxP len live h) := by
  iintro #Hrr
  iunfold rrCode at Hrr
  icases Hrr with ⟨#HcR, #Hv, #F524, #F440, #F435, #F761⟩
  ihave #Hcode : ifaceCode e inst mi A n mx $$ []
  · iunfold ifaceCodeR at HcR
    icases HcR with ⟨#H, -⟩
    iexact H
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  ihave #F687 : A 687 ↪[wf] FuncInst.wasm types[31]! inst f687 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha524 := hm.funcs 524 (by decide)
  have ha687 := hm.funcs 687 (by decide)
  have ha435 := hm.funcs 435 (by decide)
  have ha761 := hm.funcs 761 (by decide)
  have t5 : types[5]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t21 : types[21]!.params.length = 0 := by rfl
  have hlt := s.toNat_lt
  have h48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h48]; omega
  have e24 : (s - 48 + 24).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h48]; omega
  have e32 : (s - 48 + 32).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h48]; omega
  have e64 : (s - 48 - 16).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have e80 : (s - 48 - 16 - 16).toNat = s.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, e64] <;> omega
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : (ob.drop 4).length = 8 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre523 at HP
  icases HP with ⟨%hargs, Hg, HI, Hs, Hvt, Hinv, Ho, Hhost⟩
  subst hargs
  ihave HI := iface_of_ifaceR n ta A $$ HI
  icases HI with ⟨HI, HS12⟩
  -- the stack: P (80) Q1 (16) Q2 (8) Q3 (8) Q4 (8) T (8) V (8) I (8) W (16)
  icases stk_split n (s.toNat - 160) 80 80 $$ Hs with ⟨P, Hs⟩
  icases stk_split n (s.toNat - 160 + 80) 16 64 $$ Hs with ⟨Q1, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16) 8 56 $$ Hs with ⟨Q2, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8) 8 48 $$ Hs with ⟨Q3, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8 + 8) 8 40 $$ Hs with ⟨Q4, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8 + 8 + 8) 8 32 $$ Hs with ⟨T, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8 + 8 + 8 + 8) 8 24 $$ Hs with ⟨V, Hs⟩
  icases stk_split n (s.toNat - 160 + 80 + 16 + 8 + 8 + 8 + 8 + 8) 8 16 $$ Hs with ⟨I, W⟩
  rw [show s.toNat - 160 + 80 = s.toNat - 80 by omega] at *
  rw [show s.toNat - 80 + 16 = s.toNat - 64 by omega, show s.toNat - 64 + 8 = s.toNat - 56 by omega,
    show s.toNat - 56 + 8 = s.toNat - 48 by omega, show s.toNat - 48 + 8 = s.toNat - 40 by omega,
    show s.toNat - 40 + 8 = s.toNat - 32 by omega, show s.toNat - 32 + 8 = s.toNat - 24 by omega,
    show s.toNat - 24 + 8 = s.toNat - 16 by omega]
  iunfold stk at Q3 T V I
  icases Q3 with ⟨%q3, %hq3, Q3⟩
  icases T with ⟨%tb, %htb, T⟩
  icases V with ⟨%vb, %hvb, V⟩
  icases I with ⟨%ib, %hib, I⟩
  icases stk_frame4 n (s.toNat - 80) (s - 48 - 16 - 16) e80 $$ Q1 with ⟨%w0, %w4, %w8, %w12, Q1⟩
  simp only [f523, cost523]
  have hge := costRest_ge cfg h (h.registers r.toNat)
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [I]
  mstep; mstep; mstep; mstep
  mcall (f524_spec cfg lim (d + 1) types[5]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      ⟨gt, .i32 (s - 48)⟩ (s - 48) rfl (by omega) (by omega) (s - 48 + 8) r q3 tb vb hq3 htb hvb
      w0 w4 w8 w12 h) using [Hg HI Q3 Q1 T V Hhost]
  · iunfold RegisterLen.pre
    ihave Q3 := memBytes_addr (show s.toNat - 56 = (s - 48 - 16).toNat + 8 by omega) $$ Q3
    ihave T := memBytes_addr (show s.toNat - 40 = (s - 48 + 8).toNat by omega) $$ T
    ihave V := memBytes_addr (show s.toNat - 32 = (s - 48 + 8).toNat + 8 by omega) $$ V
    iframe Hg HI Q3 Q1 T V Hhost
    ipureintro; rfl
  iunfold RegisterLen.post at HQ
  icases HQ with ⟨%hrs, Hg, HI, Q3, Q1, T, V, Hhost⟩
  subst hrs
  rw [e8, show (s - 48 - 16).toNat + 8 = s.toNat - 56 by omega]
  have ho4 : (ob.take 4).length = 4 := by simp; omega
  rcases hrc : h.registers r.toNat with _ | data
  · ---------------------------------------------------------------- None
    try rw [hrc]
    simp only [costRest]
    rw [lenU64_none hrc, show optTag u64Max = 0 by decide]
    mcredits (27 * cfg.regularOpCost + R)
    ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
    icases Ho with ⟨Ho0, Ho4⟩
    mstep; mstep; mstep; mstep [T]
    simp only [decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
    mstep; mstep; mstep
    mcall (f761_spec cfg lim (d + 1) types[21]! (by rfl) inst mi Cg) using []
    · ipureintro; simp
    icases HQ with %hrs
    subst hrs
    mstep; mstep; mstep [Ho0]
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 48 + 48 = s by simp]
    mcredits R
    iframe Hc
    iunfold post523
    try rw [hrc]
    simp only [optVecAt]
    isplitr
    · ipureintro; simp [htype]
    iframe Hg Hvt Hhost Ho0 Hinv
    isplitl [HI HS12]
    · iunfold ifaceR; iframe HI HS12
    isplitr [Ho4]
    · iapply stk160_join n s.toNat hs
      ihave Q1 := frame4_stk n (s.toNat - 80) _ e80 _ _ _ _ $$ Q1
      ihave Q3 := stk_bytes n _ _ 8 (by simp) $$ Q3
      ihave T := stk_bytes n _ _ 8 (by simp) $$ T
      ihave V := stk_bytes n _ _ 8 (by simp) $$ V
      ihave I := stk_bytes n _ _ 8 (by simp) $$ I
      rw [show s.toNat - 40 + 8 = s.toNat - 32 by omega]
      iframe P Q1 Q2 Q3 Q4 T V I W
    iexists ob.drop 4; iframe Ho4; ipureintro; simp; omega
  · ---------------------------------------------------------------- Some
    try rw [hrc] at hok
    obtain ⟨hdpos, hd28, hroom⟩ := hok
    try rw [hrc]
    simp only [costRest]
    have hcN : (UInt32.ofNat data.length).toNat = data.length := by simp; omega
    rw [lenU64_some hrc, tag_some data.length (by omega)]
    mcredits (65 * cfg.regularOpCost + cost687 cfg 0 (UInt32.ofNat data.length) +
      (237 * cfg.regularOpCost + readRegisterUse h data.length) + R)
    mstep; mstep; mstep; mstep [T]
    simp only [decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
    mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep; mstep [V]
    simp only [decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
    mstep
    rw [wrap_ofNat]
    icases stk_split n (s.toNat - 16) 12 4 $$ W with ⟨W, W12⟩
    iunfold stk at W
    icases W with ⟨%wb, %hwb, W⟩
    mcall (f687_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 48)
        (s - 48 + 32) 0 (UInt32.ofNat data.length) idx maxP len live wb hwb (by omega) (by omega)
        (fun _ => hroom) (by omega)) using [Hg P Q1 Q2 Q3 Hvt Hinv W]
    · iunfold pre687
      ihave Q1 := frame4_stk n (s.toNat - 80) _ e80 _ _ _ _ $$ Q1
      ihave Q3 := stk_bytes n _ _ 8 (by simp) $$ Q3
      ihave P := stk112_join' n s.toNat hs $$ [P Q1 Q2 Q3]
      · iframe P Q1 Q2 Q3
      ihave P := stk_addr (show s.toNat - 160 = (s - 48).toNat - 112 by omega) $$ P
      ihave W := memBytes_addr (show s.toNat - 16 = (s - 48 + 32).toNat by omega) $$ W
      iframe Hg P Hvt Hinv W
      ipureintro; rfl
    iunfold post687 at HQ
    icases HQ with ⟨%hrs, %p, Hg, P, Hvt, W0, W4, W8, HA⟩
    subst hrs
    rw [show MemSet.byteOf 0 = 0 from rfl]
    ihave HA := vecAfter_pos (by omega) $$ HA
    icases HA with ⟨%len', %⟨hp0, hl'⟩, Hinv, Hb⟩
    ihave P := stk_addr (show (s - 48).toNat - 112 = s.toNat - 160 by omega) $$ P
    icases stk_split n (s.toNat - 160) 96 16 $$ P with ⟨P, PQ⟩
    icases stk_frame4 n (s.toNat - 160 + 96) (s - 48 - 16) (by omega) $$ PQ with ⟨%v0, %v4, %v8, %v12, PQ⟩
    mcredits (40 * cfg.regularOpCost + (237 * cfg.regularOpCost + readRegisterUse h data.length) + R)
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mcall (f435_spec cfg lim (d + 1) types[31]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
        ⟨gt, .i32 (s - 48)⟩ (s - 48) rfl (by omega) (by omega) h (s - 48 + 24) (s - 48 + 32) p r
        (List.replicate (UInt32.ofNat data.length).toNat 0) data hrc (by simp; omega) hdpos v0 v4 v8 v12)
      using [Hg HI HS12 I W0 PQ Hb Hhost]
    · iunfold withPre
      iunfold ifaceR
      ihave I := memBytes_addr (show s.toNat - 24 = (s - 48 + 24).toNat by omega) $$ I
      iframe Hg HI HS12 I W0 PQ Hb Hhost
      ipureintro; rfl
    iunfold withPost at HQ
    icases HQ with ⟨%hrs, Hg, HI, I, W0, PQ, Hb, Hhost⟩
    subst hrs
    mcredits (19 * cfg.regularOpCost + R)
    ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
    icases Ho with ⟨Ho0, Ho8⟩
    have ho8 : (ob.take 8).length = 8 := by simp; omega
    have ho8' : (ob.drop 8).length = 4 := by simp; omega
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [W8]; mstep [Ho8]
    ihave W := KeyGet.join64 n (s - 48 + 32).toNat p (UInt32.ofNat data.length) $$ [W0 W4]
    · iframe W0 W4
    mstep; mstep; mstep [W]
    rw [VecFromElem.ofNat_decode_pair]
    mstep [Ho0]
    rw [VecFromElem.storeBytes_pair64]
    mstep
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 48 + 48 = s by simp]
    mcredits R
    iframe Hc
    iunfold post523
    try rw [hrc]
    simp only [optVecAt]
    isplitr
    · ipureintro; simp [htype]
    iframe Hg Hvt Hhost
    isplitl [HI]
    · iexact HI
    isplitr [Ho0 Ho8 Hinv Hb]
    · iapply stk160_join n s.toNat hs
      ihave PQ := frame4_stk n (s.toNat - 64) _ (by omega) _ _ _ _ $$ PQ
      icases stk_split n (s.toNat - 64) 8 8 $$ PQ with ⟨Q2, Q3⟩
      icases stk_split n (s.toNat - 160) 80 16 $$ P with ⟨P, Q1⟩
      ihave T := stk_bytes n _ _ 8 (by simp) $$ T
      ihave V := stk_bytes n _ _ 8 (by simp) $$ V
      ihave I := stk_bytes n _ _ 8 (by simp) $$ I
      ihave W := KeyGet.split64 n _ p _ $$ W
      icases W with ⟨W0, W4⟩
      ihave W0 := stk_word n _ p $$ W0
      ihave W4 := stk_word n _ _ $$ W4
      ihave W8 := stk_word n _ _ $$ W8
      ihave W := stk_join n _ 4 4 $$ [W0 W4]
      · iframe W0 W4
      ihave W := stk_join n _ 8 4 $$ [W W8]
      · iframe W W8
      ihave W := stk_join n _ 12 4 $$ [W W12]
      · rw [e32]; iframe W W12
      rw [show s.toNat - 160 + 80 = s.toNat - 80 by omega, show s.toNat - 64 + 8 = s.toNat - 56 by omega,
        show s.toNat - 40 + 8 = s.toNat - 32 by omega, e24]
      iframe P Q1 Q2 Q3 Q4 T V I
      iexact W
    iexists p
    ihave Ho0 := KeyGet.split64 n out.toNat p _ $$ Ho0
    icases Ho0 with ⟨Ho0, Ho4⟩
    iframe Ho0 Ho4 Ho8
    iexists len'
    rw [hcN]
    iframe Hinv Hb
    ipureintro; exact ⟨hp0, hl'⟩

end Spec

end WNear.Binary.ReadRegister
