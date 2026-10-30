import Bridge.Functions.Borrow

/-!
# `env::register_len` (function 524), through the blockchain interface

```wat
;; 524 register_len(out, id): Option<u64> at out
sp -= 16;  [sp+8] := id (i64)
v := call 440(1055020, sp + 8)              ;; BLOCKCHAIN_INTERFACE.with(|b| b.register_len(id))
[out+8] := v;  [out] := (v != u64::MAX)     ;; Some(v) unless the register is unset
sp += 16

;; 440 LocalKey::with(key, &id) -> u64
sp -= 16
c := call_indirect[*key]()                  ;; __getit (565): the RefCell 1074904
call 429(sp, c, loc)                        ;; RefCell::borrow: the Ref (c + 4, c) at sp
[sp+12], [sp+8] := [sp+4], [sp]
b := expect(select(c + 4, 0, [c + 4]))      ;; 430 on Some
v := call_indirect[[[b + 4] + 16]]([b], [&id])   ;; the vtable's register_len, index 39
call 431((sp + 8) | 4)                      ;; the Ref dropped
v := call 432(0, v)                         ;; Result::expect on Ok
sp += 16

;; 241: local.get 1  call 1                 ;; the register_len host
```

* `f241_spec`: the trampoline: 2 instructions and the host's `registerLenUse h`
  (`registerLen_readContract`).
* `f440_spec`: `LocalKey::with` on an installed interface (`Interface.iface`,
  handed back): 243 `regular_op_cost`s and `registerLenUse h`.
* `f524_spec`: `env::register_len(out, id)`: 281 and `registerLenUse h`; it
  writes `Some(len)` (tag 1, `len` the register's length) or `None` (tag 0,
  the register unset; the payload is `u64::MAX`) at `out`, the host unchanged
  (`mhostPt h` in and out).

Known `mstep` issue met here: a load whose address is a local holding a
`UInt32.ofNat k` literal (left by an earlier `local.tee` of a loaded word)
fails with "No goals to be solved"; `simp only [UInt32.reduceOfNat]` first
works around it.
-/

namespace WNear.Binary.RegisterLen

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-! ## Facts -/

theorem decodeLE_storeBytes_i64 (v : UInt64) : Memory.decodeLE (storeBytes (.i64 v) 8) = v.toNat := by
  have hv := v.toNat_lt
  simp [storeBytes, storeRaw, Memory.decodeLE, List.range, List.range.loop, Nat.shiftRight_eq_div_pow]
  omega

theorem load_storeBytes_i64 (v : UInt64) :
    loadValue .i64 none (Memory.decodeLE (storeBytes (.i64 v) 8)) = .i64 v := by
  simp [loadValue, decodeLE_storeBytes_i64]

theorem storeBytes_i64_length (v : UInt64) : (storeBytes (.i64 v) 8).length = 8 := by
  simp [storeBytes]

/-- What `register_len` returns, as a `u64`. -/
def registerLenU64 (h : NearState) (r : UInt64) : UInt64 :=
  match h.registers r.toNat with
  | none => u64Max
  | some data => UInt64.ofNat data.length

theorem registerLenResult_eq (h : NearState) (r : UInt64) :
    registerLenResult h r = .i64 (registerLenU64 h r) := by
  unfold registerLenResult registerLenU64
  split <;> simp [*]

/-- The tag of the `Option<u64>` `register_len` returns: 0 (`None`) when the
register is unset. -/
def optTag (v : UInt64) : UInt64 := if v = u64Max then 0 else 1

theorem tag_eq (v : UInt64) :
    (Numeric.bool (Numeric.irelop64 IRelOp.ne v 18446744073709551615)).toUInt64 = optTag v := by
  unfold optTag
  by_cases hv : v = 18446744073709551615 <;> simp [Numeric.bool, Numeric.irelop64, hv, u64Max]

theorem or_four (x : UInt32) (h : x.toNat % 8 = 0) (hb : x.toNat + 12 < 2 ^ 32) :
    (x + 8) ||| 4 = x + 12 := by
  apply UInt32.toNat_inj.1
  simp only [UInt32.toNat_or, UInt32.toNat_add, UInt32.reduceToNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have e := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := 4) (by decide) ((x.toNat + 8) / 8)
  have m : 2 ^ 3 * ((x.toNat + 8) / 8) = x.toNat + 8 := by omega
  rw [m] at e
  omega

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}
  {Cg K : Nat}

theorem memBytes_nil (n i : Nat) : ⊢ memBytes (H := NearState) (GF := GF) n i [] :=
  by unfold WasmLogic.memBytes byteCells; iapply BigSepL.bigSepL_nil.2; iempintro

/-- `mwpi_call_host_ro` on a stack holding just the arguments, the credits
any `K` covering the call and the host's gas. -/
theorem mwpi_call_host_ro' (i a n ptr : Nat) (fn : HostFn NearState) (h h' : NearState)
    (mx : Option Nat) (bs : List UInt8) (args rs : List Value) {kh : Nat}
    (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length)
    (hc : ReadContract fn h h' args rs ptr bs kh Cg) :
    credits Cg K ∗ ⌜cfg.regularOpCost + kh ≤ K⌝ ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗
      mhostPt h ∗ n ↦[wms][ ptr ] bs ∗
      ▷ (mhostPt h' -∗ n ↦[wms][ ptr ] bs -∗ credits Cg (K - (cfg.regularOpCost + kh)) -∗
        Φ.normal rs f)
      ⊢ mwpi cfg lim d f args [.call i] Φ := by
  iintro ⟨Hc, %hK, Hf, Hm, Hh, Hb, H⟩
  have r := mwpi_call_host_ro (cfg := cfg) (lim := lim) (d := d) (f := f) (Φ := Φ)
    (R := K - (cfg.regularOpCost + kh)) i a n ptr fn h h' mx bs [] args rs ha hn hlen hc
  simp only [List.nil_append] at r
  iapply r
  rw [show cfg.regularOpCost + kh + (K - (cfg.regularOpCost + kh)) = K by omega]
  iframe Hc Hf Hm Hh Hb H

end Flex

/-! ## The trampoline (241) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def trampPre (h : NearState) (dp : UInt32) (r : UInt64) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 r]⌝ ∗ mhostPt h)

def trampPost (h : NearState) (r : UInt64) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 (registerLenU64 h r)]⌝ ∗ mhostPt h)

/-- `VmBlockchainInterface::register_len` (241, the vtable's index 39):
`register_len(r)` (import 1), the host unchanged but for gas. -/
theorem f241_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e n a1 : Nat)
    (mx : Option Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[1]? = some a1)
    (Cg : Nat) (h : NearState) (dp : UInt32) (r : UInt64) :
    a1 ↪[wf] FuncInst.host (metered e "register_len" registerLenFn).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f241 Cg (trampPre h dp r)
        (fun _ => 2 * cfg.regularOpCost + registerLenUse h) (trampPost h r) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hhost⟩
  subst hargs
  simp only [f241]
  mstep
  have hc := registerLen_readContract (C := Cg) e h r 0
  rw [registerLenResult_eq] at hc
  iapply mwpi_call_host_ro' 1 a1 n 0 _ h h mx [] [.i64 r] [.i64 (registerLenU64 h r)] ha hn rfl hc
  iframe Hc Hh Hm Hhost
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitr
  · iapply memBytes_nil
  inext
  iintro Hhost - Hc
  mpay with simp [htype]
  mcredits R
  iframe Hc
  iunfold trampPost
  iframe Hhost
  ipureintro; simp [htype]

end Tramp

/-! ## `LocalKey::with` (440), the interface installed -/

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Four words at `fp`: the frame of `LocalKey::with`. -/
def frame4 (n : Nat) (fp : UInt32) (w0 w4 w8 w12 : UInt32) : IProp GF :=
  iprop(n ↦[i32][ fp.toNat ] w0 ∗ n ↦[i32][ fp.toNat + 4 ] w4 ∗ n ↦[i32][ fp.toNat + 8 ] w8 ∗
    n ↦[i32][ fp.toNat + 12 ] w12)

/-- The key 1055020 and a pointer to the register id; the stack pointer, the
interface, the id's bytes, the frame below `sp` and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp regp : UInt32) (r : UInt64)
    (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 regp]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[wms][ regp.toNat ] storeBytes (.i64 r) 8 ∗ frame4 n (sp - 16) w0 w4 w8 w12 ∗ mhostPt h)

/-- The register's length (or `u64::MAX`); the interface back as it was, the
frame holding the dropped `Ref`. -/
def withPost (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp regp : UInt32) (r : UInt64)
    (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i64 (registerLenU64 h r)]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[wms][ regp.toNat ] storeBytes (.i64 r) 8 ∗
    frame4 n (sp - 16) 1074908 1074904 1074908 1074904 ∗ mhostPt h)

/-- `BLOCKCHAIN_INTERFACE.with(|b| b.register_len(id))` (440) on the
installed interface: 243 `regular_op_cost`s and the host's gas. -/
theorem f440_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (regp : UInt32) (r : UInt64) (w0 w4 w8 w12 : UInt32)
    (h : NearState) :
    ifaceCode e inst mi A n mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f440 Cg
        (withPre n g ta A gi sp regp r w0 w4 w8 w12 h)
        (fun _ => 243 * cfg.regularOpCost + registerLenUse h) (withPost n g ta A gi sp regp r h) := by
  iintro #Hcode
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, Hreg, HF, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, ⟨S16, T39⟩, S92, S188⟩
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
  have ha429 := hm.funcs 429 (by decide)
  have ha430 := hm.funcs 430 (by decide)
  have ha431 := hm.funcs 431 (by decide)
  have ha432 := hm.funcs 432 (by decide)
  have t429 : types[31]!.params.length = 3 := by rfl
  have t430 : types[13]!.params.length = 2 := by rfl
  have t431 : types[0]!.params.length = 1 := by rfl
  have t432 : types[24]!.params.length = 2 := by rfl
  have hg := hm.glob
  have hn := hm.mem
  simp only [f440]
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
      (sp - 16) 1074904 1055224 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  -- `Some`: the box
  mstep; mstep
  simp only [UInt32.reduceOfNat]
  mstep
  mstep [Hda]
  simp only [UInt32.reduceOfNat]
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1055240
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `register_len`
  mstep; mstep [Hda]; mstep; mstep [Hreg] with simp [storeBytes]
  simp only [decodeLE_storeBytes_i64, UInt64.ofNat_toNat]
  mstep; mstep [Hvt]
  simp only [UInt32.reduceOfNat]
  mstep [S16]
  simp only [UInt32.reduceOfNat]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 7) (t := 0) (ta := ta) (idx := 39) (a := A 241)
    (type := types[7]!) (inst := inst) (mi := mi) (code := f241) [.i32 1, .i64 r])
  isplitr
  · iapply (f241_spec cfg lim (d + 1) types[7]! (by rfl) inst mi e n (A 1) mx hm.mem
      (hm.funcs 1 (by decide)) Cg h 1 r)
    mpersist
  isplitr
  · iexact F241
  isplitr
  · iexact Hi
  isplitl [T39]
  · simp only [UInt32.reduceToNat]; iexact T39
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hhost]
  · iunfold trampPre
    iframe Hhost
    ipureintro; rfl
  inext
  iintro %rs T39 Hc HQ
  iunfold trampPost at HQ
  icases HQ with ⟨%hrs, Hhost⟩
  subst hrs
  mctrl_norm
  mstep
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
  mstep; mstep; mstep
  -- `Result::expect`
  mstep; mstep
  mcall (Borrow.f432_spec cfg lim (d + 1) types[24]! (by rfl) inst mi g hm.glob Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl (registerLenU64 h r)) using [Hg]
  · iunfold Borrow.resultPre
    iframe Hg
    ipureintro; rfl
  iunfold Borrow.resultPost at HQ
  icases HQ with ⟨%hrs, Hg⟩
  subst hrs
  -- sp += 16
  mstep; mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e]
  mstep
  mcredits R
  iframe Hc
  iunfold withPost, iface, slot, blockchainInterfaceCells, frame4
  simp only [UInt32.reduceToNat, Nat.reduceAdd]
  iframe Hg Hkey T116 Hst Hfl Hda Hvt S16 T39 S92 S188 Hreg W0 W4 W8 W12 Hhost
  ipureintro; simp [htype]

end With

/-! ## `env::register_len` (524) -/

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The out pointer and the register id; the stack pointer, the installed
interface, the 8 bytes of 524's frame (at `sp - 8`) and the 16 bytes of
`LocalKey::with`'s (at `sp - 32`), the 16 bytes at `out`, the host. -/
def pre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp out : UInt32) (r : UInt64)
    (rb ob0 ob8 : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i64 r]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[wms][ (sp - 16).toNat + 8 ] rb ∗ frame4 n (sp - 16 - 16) w0 w4 w8 w12 ∗
    n ↦[wms][ out.toNat ] ob0 ∗ n ↦[wms][ out.toNat + 8 ] ob8 ∗ mhostPt h)

/-- `Option<u64>` at `out`: the tag `optTag v` (1 for `Some`, 0 for `None`)
and the payload `v`, the register's length (`u64::MAX` when unset); the
interface back, the host unchanged. -/
def post (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp out : UInt32) (r : UInt64)
    (h : NearState) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗
    n ↦[wms][ (sp - 16).toNat + 8 ] storeBytes (.i64 r) 8 ∗
    frame4 n (sp - 16 - 16) 1074908 1074904 1074908 1074904 ∗
    n ↦[wms][ out.toNat ] storeBytes (.i64 (optTag (registerLenU64 h r))) 8 ∗
    n ↦[wms][ out.toNat + 8 ] storeBytes (.i64 (registerLenU64 h r)) 8 ∗ mhostPt h)

/-- **`env::register_len(id)`** (function 524 of `contract.wasm`) on the
installed blockchain interface: 281 `regular_op_cost`s and the host's
`registerLenUse h`; `Some(len)` or `None` at `out`. -/
theorem f524_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 32 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (out : UInt32) (r : UInt64) (rb ob0 ob8 : List UInt8)
    (hrb : rb.length = 8) (hob0 : ob0.length = 8) (hob8 : ob8.length = 8)
    (w0 w4 w8 w12 : UInt32) (h : NearState) :
    A 440 ↪[wf] FuncInst.wasm types[30]! inst f440 ∗ ifaceCode e inst mi A n mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f524 Cg
        (pre n g ta A gi sp out r rb ob0 ob8 w0 w4 w8 w12 h)
        (fun _ => 281 * cfg.regularOpCost + registerLenUse h) (post n g ta A gi sp out r h) := by
  iintro ⟨#F440, #Hcode⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold ifaceCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, HI, Hrb, HF, Ho0, Ho8, Hhost⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have hg := hm.glob
  have hn := hm.mem
  have ha440 := hm.funcs 440 (by decide)
  have t440 : types[30]!.params.length = 2 := by rfl
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  simp only [f524]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [Hrb]
  mstep; mstep; mstep; mstep; mstep
  mcall (f440_spec cfg lim (d + 1) types[30]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl (by omega) (by omega) (sp - 16 + 8) r
      w0 w4 w8 w12 h) using [Hg HI Hrb HF Hhost]
  · iunfold withPre
    rw [e8]
    iframe Hg HI Hrb HF Hhost
    ipureintro; rfl
  iunfold withPost at HQ
  icases HQ with ⟨%hrs, Hg, HI, Hrb, HF, Hhost⟩
  subst hrs
  rw [e8]
  mstep; mstep [Ho8]
  mstep; mstep; mstep; mstep; mstep; mstep [Ho0]
  mstep; mstep; mstep; mstep [Hg]
  have e : sp - 16 + 16 = sp := by simp
  rw [e, tag_eq]
  mcredits R
  iframe Hc
  iunfold post
  iframe Hg HI Hrb HF Ho0 Ho8 Hhost
  ipureintro; rfl

end Spec

end WNear.Binary.RegisterLen
