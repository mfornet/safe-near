import Bridge.Functions.RegisterLen
import Binary.Code.Part01
import Binary.Code.Part09
import Binary.Code.Part10
import NearLogic.Hosts.PanicUtf8
import NearLogic.Rules.CallIndirectSpec

/-!
# `env::panic_str` (function 521) and `Contract::default` (156), down to `panic_utf8`

```wat
;; 156 Contract::default under PanicOnDefault
call 521(1050868, 31)                       ;; "The contract is not initialized"
unreachable

;; 521 panic_str(ptr, len)
sp -= 16;  [sp+12] := len;  [sp+8] := ptr
call 448(1055020, sp + 8)                   ;; BLOCKCHAIN_INTERFACE.with(|b| b.panic_utf8(msg))
call 853(1055964, 40, 1056180)  unreachable ;; not reached: the host traps

;; 448 LocalKey::with(key, &(ptr, len))
sp -= 16
c := call_indirect[*key]()                  ;; __getit (565): the RefCell 1074904
call 429(sp, c, loc)                        ;; RefCell::borrow: the Ref (c + 4, c) at sp
[sp+12], [sp+8] := [sp+4], [sp]
b := expect(select(c + 4, 0, [c + 4]))      ;; 430 on Some
call_indirect[[[b + 4] + 100]]([b], [&m + 4] as u64, [&m] as u64)   ;; panic_utf8, index 60
...                                         ;; not reached

;; 262: local.get 1  local.get 2  call 22   ;; the panic_utf8 host (len, ptr)
```

The vtable word at `1050188 + 100` is the table index 60 (`vtable_panicUtf8`), whose entry is
the trampoline 262; `panic_utf8` is import 22. `Interface.iface` does not own that slot:
`panicSlot` holds it, and `panicCode` the trampoline's and the host's code.

None of these functions returns: each spec is an `MFunSpecT` whose normal postcondition is
`False` and whose trap postcondition is `panicked Cg h bs`, a host that differs from `h` (up to
gas) only in its last error, `GuestPanic (utf8String bs)`, and the gas counter, still within
`Cg` (what bounds the gas a run that panics uses). Everything else is dropped on the trap.

* `f262_spec`: the trampoline: 3 `regular_op_cost`s and `panicUtf8Use h len`.
* `f448_spec`: `LocalKey::with` on the installed interface: 168 and `panicUtf8Use h len`.
* `f521_spec`: `env::panic_str(ptr, len)`: 194 and `panicUtf8Use h len`.
* `f156_spec`: `Contract::default`: 207 and `panicUtf8Use h 31`, the message
  `"The contract is not initialized"` (`notInit_utf8String`).

The premises are the host contract's (`panicUtf8_trapContract`): a nonempty valid UTF-8
message that fits the log limit (`LogFits`) and whose `read_memory_byte` cost fits a `u64`.
-/

namespace WNear.Binary.PanicStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface
open WNear.Binary.RegisterLen (frame4)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)

/-! ## The data -/

/-- `panic_utf8`: the table index 60. -/
theorem vtable_panicUtf8 : dataWord (1050188 + 100) = bytes32 60 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entry 60: the trampoline 262. -/
theorem wTable_panicUtf8 : wTable.elems[60]? = some (Ref.func 262) := rfl

/-- The trampoline's import: `panic_utf8` (22), as the instantiated store holds it. -/
theorem wStore_panicUtf8 (cfg : RuntimeConfig) (h : NearState) :
    (wStore cfg h).funcs[22]? =
      some (FuncInst.host (metered cfg.fees.numExtraBytesRecord "panic_utf8" panicUtf8Metered).toHostFn) := by
  simp [wStore, wHosts]

/-- `"The contract is not initialized"`, the message of `PanicOnDefault`. -/
def notInit : List UInt8 :=
  [84, 104, 101, 32, 99, 111, 110, 116, 114, 97, 99, 116, 32, 105, 115, 32, 110, 111, 116, 32, 105, 110, 105,
    116, 105, 97, 108, 105, 122, 101, 100]

theorem notInit_eq : notInit = "The contract is not initialized".toUTF8.toList := by decide +kernel

/-- The 31 bytes of the data segment at 1050868. -/
theorem notInit_data :
    (List.range 31).map (fun k => wNearSource.read (159306 + (1050868 - 1048576) + k)) = notInit := by
  decide

theorem notInit_length : notInit.length = 31 := by decide

theorem notInit_valid : validUtf8 notInit = true := by decide

theorem notInit_utf8String : utf8String notInit = "The contract is not initialized" := by
  decide +kernel

/-! ## The resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The vtable slot of `panic_utf8`: the table index 60 at `1050188 + 100`, and its entry. -/
def panicSlot (n ta : Nat) (A : Nat → Nat) : IProp GF := slot n ta 100 60 (A 262)

/-- The trampoline and the `panic_utf8` host (persistent). -/
def panicCode (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(A 262 ↪[wf] FuncInst.wasm types[4]! inst f262 ∗
    A 22 ↪[wf] FuncInst.host (metered e "panic_utf8" panicUtf8Metered).toHostFn ∗
    inst ↪[inst] mi)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (panicCode (GF := GF) e inst mi A) := by
  unfold panicCode; infer_instance

/-- From the data segment's word at `1050188 + 100` and the table entry 60. -/
theorem panicSlot_of (n ta : Nat) (A : Nat → Nat) :
    n ↦[wms][ 1050188 + 100 ] dataWord (1050188 + 100) ∗ ta ↦[wt][ 60 ] Ref.func (A 262)
      ⊢ panicSlot (GF := GF) n ta A := by
  rw [vtable_panicUtf8]
  iintro ⟨H, T⟩
  iunfold panicSlot, slot
  simp only [UInt32.reduceToNat]
  iframe H T

/-- **The host panicked** with the message `bs`: up to gas, `h` with the last error
`GuestPanic (utf8String bs)`; and the gas counter, its use still within `Cg`. -/
def panicked (Cg : Nat) (h : NearState) (bs : List UInt8) : IProp GF :=
  iprop(∃ h', ⌜erase h' = erase { h with lastError := some (.guestPanic (utf8String bs)) }⌝ ∗
    mhostPt h' ∗ ∃ R, credits Cg R)

end Res

/-! ## The trampoline (262) -/

section Tramp

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}
  {Cg K : Nat}

/-- `mwpi_call_host_trap` on a stack holding just the arguments, the credits any `K`
covering the call and the host's gas; the trap keeps the credits left. -/
theorem mwpi_call_host_trap' (i a n ptr : Nat) (fn : HostFn NearState) (h : NearState)
    (Q : NearState → Prop) (mx : Option Nat) (bs : List UInt8) (args : List Value) (r : Trap)
    {kh : Nat} (ha : f.mi.funcAddrs[i]? = some a) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : args.length = fn.type.params.length) (hc : TrapContractP fn h Q args r ptr bs kh Cg) :
    credits Cg K ∗ ⌜cfg.regularOpCost + kh ≤ K⌝ ∗ a ↪[wf] FuncInst.host fn ∗ n ↪[wmlimit] mx ∗
      mhostPt h ∗ n ↦[wms][ ptr ] bs ∗
      ▷ (∀ h', ⌜Q h'⌝ -∗ mhostPt h' -∗ (∃ R, credits Cg R) -∗ Φ.trap)
      ⊢ mwpi cfg lim d f args [.call i] Φ := by
  iintro ⟨Hc, %hK, Hf, Hm, Hh, Hb, H⟩
  have r := mwpi_call_host_trap (cfg := cfg) (lim := lim) (d := d) (f := f) (Φ := Φ)
    (R := K - (cfg.regularOpCost + kh)) i a n ptr fn h Q mx bs [] args r ha hn hlen hc
  simp only [List.nil_append] at r
  iapply r
  rw [show cfg.regularOpCost + kh + (K - (cfg.regularOpCost + kh)) = K by omega]
  iframe Hc Hf Hm Hh Hb
  inext
  iintro %h' %hq Hh - Hc
  iapply H $$ %h' %hq Hh
  iexists _
  iexact Hc

def trampPre (n : Nat) (h : NearState) (dp : UInt32) (len ptr : UInt64) (bs : List UInt8)
    (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dp, .i64 len, .i64 ptr]⌝ ∗ n ↦[wms][ ptr.toNat ] bs ∗ mhostPt h)

/-- `VmBlockchainInterface::panic_utf8` (262, the vtable's index 60): `panic_utf8(len, ptr)`
(import 22), which traps with the message `bs`. -/
theorem f262_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e n a22 : Nat) (mx : Option Nat)
    (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[22]? = some a22) (Cg : Nat)
    (h : NearState) (dp : UInt32) (len ptr : UInt64) (bs : List UInt8) (hlen : len ≠ u64Max)
    (hkl : bs.length = len.toNat) (hpos : 0 < len.toNat) (hutf : validUtf8 bs = true)
    (hfit : LogFits h len.toNat)
    (hov : h.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64) :
    a22 ↪[wf] FuncInst.host (metered e "panic_utf8" panicUtf8Metered).toHostFn ∗ n ↪[wmlimit] mx
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f262 Cg (trampPre n h dp len ptr bs)
        (fun _ => 3 * cfg.regularOpCost + panicUtf8Use h len.toNat) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h bs) := by
  iintro ⟨#Hh, #Hm⟩
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold trampPre at HP
  icases HP with ⟨%hargs, Hb, Hhost⟩
  subst hargs
  simp only [f262]
  mstep; mstep
  have hc := panicUtf8_trapContract (C := Cg) e h len ptr bs hlen hkl hpos hutf hfit hov
  iapply mwpi_call_host_trap' 22 a22 n ptr.toNat _ h _ mx bs [.i64 len, .i64 ptr] _ ha hn rfl hc
  iframe Hc Hh Hm Hhost Hb
  isplitr
  · ipureintro; mstep_norm_full; omega
  inext
  iintro %h' %hq Hhost Hc
  simp only [Post.mfunc]
  iunfold panicked
  iexists h'
  iframe Hhost Hc
  ipureintro; exact hq

end Tramp

/-! ## `LocalKey::with` (448), the interface installed -/

theorem loadValue_i64_u32 (r : Nat) :
    loadValue .i64 (some { bits := 32, signed := false }) r = .i64 (UInt64.ofNat r) := rfl

theorem u64_toNat (x : UInt32) : (UInt64.ofNat x.toNat).toNat = x.toNat := by
  have := x.toNat_lt
  simp only [UInt64.toNat_ofNat']
  omega

theorem u64_ne (x : UInt32) : UInt64.ofNat x.toNat ≠ u64Max := by
  intro hc
  have e := congrArg UInt64.toNat hc
  rw [u64_toNat] at e
  have := x.toNat_lt
  simp [u64Max] at e
  omega

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

/-- `Borrow.mwpi_call_indirect'` for a callee that may trap (`MFunSpecT`). -/
theorem mwpi_call_indirectT' {ty t ta : Nat} {idx : UInt32} {a : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {P : List Value → IProp GF} {Kf : List Value → Nat}
    {Q : List Value → List Value → IProp GF} {T : List Value → IProp GF} (args : List Value) :
    MFunSpecT cfg lim (d + 1) type inst mi code Cg P Kf Q T ∗
      a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗ ta ↦[wt][ idx.toNat ] Ref.func a ∗
      ⌜vs = args ++ [.i32 idx] ∧ f.mi.tableAddrs[t]? = some ta ∧ type = f.mi.types[ty]! ∧
        args.length = type.params.length ∧ d + 1 < lim.maxCallDepth⌝ ∗
      credits Cg K ∗
      ⌜cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) + Kf args ≤ K⌝ ∗
      P args ∗
      ▷ ((∀ rs, ta ↦[wt][ idx.toNat ] Ref.func a -∗
          credits Cg (K - (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
            Kf args)) -∗ Q args rs -∗ Φ.normal rs f) ∧ (T args -∗ Φ.trap))
      ⊢ mwpi cfg lim d f vs [.call_indirect ty t] Φ := by
  iintro ⟨Hs, Hf, Hi, Ht, %⟨hvs, hta, hty, hlen, hd⟩, Hc, %hK, HP, H⟩
  subst hvs
  have r := mwpi_call_indirect_specT (cfg := cfg) (Cg := Cg) (Φ := Φ) (R := K - (cfg.regularOpCost +
    activationGas cfg.regularOpCost (entryLocals code args) + Kf args)) ty t ta idx a type inst mi
    code [] args P Kf Q T hta hty hlen hd
  simp only [List.nil_append] at r
  iapply r
  have e : cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
      (Kf args + (K - (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        Kf args))) = K := by omega
  rw [e]
  iframe Hc Ht Hf Hi Hs HP
  iexact H

/-- `call i` of a function that may trap (`MFunSpecT`), the stack its arguments `args`. -/
theorem mwpi_callT' {i a : Nat} {type : FuncType} {inst : Nat} {mi : ModuleInst} {code : Func}
    {P : List Value → IProp GF} {Kf : List Value → Nat} {Q : List Value → List Value → IProp GF}
    {T : List Value → IProp GF} (args : List Value) :
    MFunSpecT cfg lim (d + 1) type inst mi code Cg P Kf Q T ∗
      a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      ⌜args = vs ∧ f.mi.funcAddrs[i]? = some a ∧ args.length = type.params.length ∧
        d + 1 < lim.maxCallDepth⌝ ∗
      credits Cg K ∗
      ⌜cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) + Kf args ≤ K⌝ ∗
      P args ∗
      ▷ ((∀ rs, credits Cg (K - (cfg.regularOpCost + activationGas cfg.regularOpCost
          (entryLocals code args) + Kf args)) -∗ Q args rs -∗ Φ.normal rs f) ∧ (T args -∗ Φ.trap))
      ⊢ mwpi cfg lim d f vs [.call i] Φ := by
  iintro ⟨Hs, Hf, Hi, %⟨hvs, ha, hlen, hd⟩, Hc, %hK, HP, H⟩
  subst hvs
  have r := mwpi_call_specT (cfg := cfg) (Cg := Cg) (Φ := Φ) (f := f) (R := K - (cfg.regularOpCost +
    activationGas cfg.regularOpCost (entryLocals code args) + Kf args)) i a type inst mi code [] args
    P Kf Q T ha hlen hd
  simp only [List.nil_append] at r
  iapply r
  have e : cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
      (Kf args + (K - (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        Kf args))) = K := by omega
  rw [e]
  iframe Hc Hf Hi Hs HP
  iexact H

end Flex

section With

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The key 1055020 and a pointer `cp` to the message's `(ptr, len)`; the stack pointer, the
interface and the `panic_utf8` slot, the message, the frame below `sp` and the host. -/
def withPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp cp ptr len : UInt32)
    (bs : List UInt8) (w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1055020, .i32 cp]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ panicSlot n ta A ∗
    n ↦[i32][ cp.toNat ] ptr ∗ n ↦[i32][ cp.toNat + 4 ] len ∗ n ↦[wms][ ptr.toNat ] bs ∗
    frame4 n (sp - 16) w0 w4 w8 w12 ∗ mhostPt h)

/-- `BLOCKCHAIN_INTERFACE.with(|b| b.panic_utf8(msg))` (448) on the installed interface, the
message the `len` bytes `bs` at `ptr`: it traps, the host panicked with `bs`. -/
theorem f448_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 16 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (cp ptr len : UInt32) (bs : List UInt8) (hkl : bs.length = len.toNat)
    (hpos : 0 < len.toNat) (hutf : validUtf8 bs = true) (w0 w4 w8 w12 : UInt32) (h : NearState)
    (hfit : LogFits h len.toNat)
    (hov : h.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64) :
    ifaceCode e inst mi A n mx ∗ panicCode e inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f448 Cg
        (withPre n g ta A gi sp cp ptr len bs w0 w4 w8 w12 h)
        (fun _ => 168 * cfg.regularOpCost + panicUtf8Use h len.toNat) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h bs) := by
  iintro ⟨#Hcode, #Hpc⟩
  iunfold ifaceCode at Hcode
  icases Hcode with ⟨#F565, #F468, #F429, #F494, #F672, #F430, #F431, #F432, #F433, #F241, #F260, #F284,
    #H1, #H20, #H43, #Hm, #Hi⟩
  iunfold panicCode at Hpc
  icases Hpc with ⟨#F262, #H22, -⟩
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold withPre at HP
  icases HP with ⟨%hargs, Hg, HI, HS, Hp, Hl, Hb, HF, Hhost⟩
  subst hargs
  iunfold iface, slot, blockchainInterfaceCells at HI
  icases HI with ⟨Hkey, T116, ⟨Hst, Hfl, Hda, Hvt⟩, -, -, -⟩
  iunfold panicSlot, slot at HS
  icases HS with ⟨S100, T60⟩
  iunfold frame4 at HF
  icases HF with ⟨W0, W4, W8, W12⟩
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have ha429 := hm.funcs 429 (by decide)
  have ha430 := hm.funcs 430 (by decide)
  have t429 : types[31]!.params.length = 3 := by rfl
  have t430 : types[13]!.params.length = 2 := by rfl
  have hg := hm.glob
  have hn := hm.mem
  simp only [f448]
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
      (sp - 16) 1074904 1056196 w0 w4 (by decide)) using [Hg Hfl W0 W4]
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
  -- the result flag
  mstep; mstep
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
  mcall (Borrow.f430_spec cfg lim (d + 1) types[13]! (by rfl) inst mi Cg 1074908 1056212
    (by decide))
  · iunfold Borrow.expectSomePre
    ipureintro; rfl
  iunfold Borrow.expectSomePost at HQ
  icases HQ with %hrs
  subst hrs
  -- the vtable's `panic_utf8`
  mstep; mstep [Hda]; mstep; mstep [Hl]; mstep; mstep [Hp]
  mstep; mstep [Hvt]
  simp only [UInt32.reduceOfNat]
  mstep [S100]
  simp only [UInt32.reduceOfNat, loadValue_i64_u32]
  iapply mwpi_cons
  iapply (mwpi_call_indirectT' (ty := 4) (t := 0) (ta := ta) (idx := 60) (a := A 262)
    (type := types[4]!) (inst := inst) (mi := mi) (code := f262)
    [.i32 1, .i64 (UInt64.ofNat len.toNat), .i64 (UInt64.ofNat ptr.toNat)])
  isplitr
  · iapply (f262_spec cfg lim (d + 1) types[4]! inst mi e n (A 22) mx hm.mem (hm.funcs 22 (by decide))
      Cg h 1 (UInt64.ofNat len.toNat) (UInt64.ofNat ptr.toNat) bs (u64_ne len)
      (by rw [u64_toNat]; exact hkl) (by rw [u64_toNat]; exact hpos) hutf
      (by rw [u64_toNat]; exact hfit) (by rw [u64_toNat]; exact hov))
    mpersist
  isplitr
  · iexact F262
  isplitr
  · iexact Hi
  isplitl [T60]
  · simp only [UInt32.reduceToNat]; iexact T60
  isplitr
  · ipureintro; exact ⟨rfl, hm.table, by simp [hm.types], by rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; rw [u64_toNat]; omega
  isplitl [Hb Hhost]
  · iunfold trampPre
    rw [u64_toNat]
    iframe Hb Hhost
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexact HT

end With

/-! ## `env::panic_str` (521) -/

section PanicStr

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The message's pointer and length; the stack pointer, the interface and the `panic_utf8`
slot, the 8 bytes of 521's frame (at `sp - 8`) and the 16 bytes of `LocalKey::with`'s (at
`sp - 32`), the message and the host. -/
def pre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp ptr len : UInt32) (bs : List UInt8)
    (c0 c4 w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 ptr, .i32 len]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ panicSlot n ta A ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] c0 ∗ n ↦[i32][ (sp - 16).toNat + 12 ] c4 ∗
    frame4 n (sp - 16 - 16) w0 w4 w8 w12 ∗ n ↦[wms][ ptr.toNat ] bs ∗ mhostPt h)

/-- **`env::panic_str(msg)`** (function 521 of `contract.wasm`) on the installed blockchain
interface, the message the `len` bytes `bs` at `ptr`: it traps, the host panicked with `bs`. -/
theorem f521_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 32 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (ptr len : UInt32) (bs : List UInt8) (hkl : bs.length = len.toNat)
    (hpos : 0 < len.toNat) (hutf : validUtf8 bs = true) (c0 c4 w0 w4 w8 w12 : UInt32)
    (h : NearState) (hfit : LogFits h len.toNat)
    (hov : h.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64) :
    A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗ ifaceCode e inst mi A n mx ∗
      panicCode e inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f521 Cg
        (pre n g ta A gi sp ptr len bs c0 c4 w0 w4 w8 w12 h)
        (fun _ => 194 * cfg.regularOpCost + panicUtf8Use h len.toNat) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h bs) := by
  iintro ⟨#F448, #Hcode, #Hpc⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at Hpc
    icases Hpc with ⟨-, -, #Hi⟩
    iexact Hi
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, HI, HS, C0, C4, HF, Hb, Hhost⟩
  subst hargs
  obtain ⟨gt, gv⟩ := gi
  simp only at hgi
  subst hgi
  have hlt := sp.toNat_lt
  have hg := hm.glob
  have hn := hm.mem
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  simp only [f521]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [C4]
  mstep; mstep; mstep [C0]
  mstep; mstep; mstep; mstep
  iapply mwpi_cons
  iapply (mwpi_callT' (i := 448) (a := A 448) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f448) [.i32 1055020, .i32 (sp - 16 + 8)])
  isplitr
  · iapply (f448_spec cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg
      { type := gt, value := .i32 (sp - 16) } (sp - 16) rfl (by omega) (by omega) (sp - 16 + 8) ptr len
      bs hkl hpos hutf w0 w4 w8 w12 h hfit hov)
    iframe Hcode Hpc
  isplitr
  · iexact F448
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, hm.funcs 448 (by decide), rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg HI HS C0 C4 HF Hb Hhost]
  · iunfold withPre
    rw [e8, show (sp - 16).toNat + 8 + 4 = (sp - 16).toNat + 12 by omega]
    iframe Hg HI HS C0 C4 HF Hb Hhost
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

end PanicStr

/-! ## `Contract::default` (156) under `PanicOnDefault` -/

section Default

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The host panicked with `"The contract is not initialized"`. -/
theorem panicked_notInit (Cg : Nat) (h : NearState) :
    panicked (GF := GF) Cg h notInit = iprop(∃ h', ⌜erase h' = erase { h with
      lastError := some (.guestPanic "The contract is not initialized") }⌝ ∗ mhostPt h' ∗
      ∃ R, credits Cg R) := by
  unfold panicked; rw [notInit_utf8String]

/-- The `self` pointer (unused); the stack pointer, the interface and the `panic_utf8` slot,
521's and `LocalKey::with`'s frames, the message at 1050868 and the host. -/
def defaultPre (n g ta : Nat) (A : Nat → Nat) (gi : GlobalInst) (sp self : UInt32)
    (c0 c4 w0 w4 w8 w12 : UInt32) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 self]⌝ ∗ g ↦[wg] gi ∗ iface n ta A ∗ panicSlot n ta A ∗
    n ↦[i32][ (sp - 16).toNat + 8 ] c0 ∗ n ↦[i32][ (sp - 16).toNat + 12 ] c4 ∗
    frame4 n (sp - 16 - 16) w0 w4 w8 w12 ∗ n ↦[wms][ 1050868 ] notInit ∗ mhostPt h)

/-- **`Contract::default`** (function 156 of `contract.wasm`, `#[derive(PanicOnDefault)]`):
`env::panic_str("The contract is not initialized")`, a trap with the host panicked with that
message (`panicked_notInit`). -/
theorem f156_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth)
    (Cg : Nat) (gi : GlobalInst) (sp : UInt32) (hgi : gi.value = .i32 sp) (hsp : 32 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (self c0 c4 w0 w4 w8 w12 : UInt32) (h : NearState)
    (hfit : LogFits h 31) (hov : h.extCosts.cost "read_memory_byte" * 31 < 2 ^ 64) :
    A 521 ↪[wf] FuncInst.wasm types[14]! inst f521 ∗ A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗
      ifaceCode e inst mi A n mx ∗ panicCode e inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f156 Cg
        (defaultPre n g ta A gi sp self c0 c4 w0 w4 w8 w12 h)
        (fun _ => 207 * cfg.regularOpCost + panicUtf8Use h 31) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h notInit) := by
  iintro ⟨#F521, #F448, #Hcode, #Hpc⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at Hpc
    icases Hpc with ⟨-, -, #Hi⟩
    iexact Hi
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold defaultPre at HP
  icases HP with ⟨%hargs, Hg, HI, HS, C0, C4, HF, Hb, Hhost⟩
  subst hargs
  simp only [f156]
  mstep; mstep
  iapply mwpi_cons
  iapply (mwpi_callT' (i := 521) (a := A 521) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f521) [.i32 1050868, .i32 31])
  isplitr
  · iapply (f521_spec cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg gi sp hgi hsp
      hal 1050868 31 notInit notInit_length (by decide) notInit_valid c0 c4 w0 w4 w8 w12 h hfit hov)
    iframe F448 Hcode Hpc
  isplitr
  · iexact F521
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, hm.funcs 521 (by decide), rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg HI HS C0 C4 HF Hb Hhost]
  · iunfold pre
    simp only [UInt32.reduceToNat]
    iframe Hg HI HS C0 C4 HF Hb Hhost
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

end Default

end WNear.Binary.PanicStr
