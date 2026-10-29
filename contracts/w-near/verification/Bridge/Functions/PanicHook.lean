import Bridge.Functions.PanicStr
import Bridge.Functions.ResultExpect
import Bridge.Functions.VecFromElem
import Binary.Code.Part09
import Binary.Code.Part14
import NearLogic.Tactic.Control

/-!
# near-sdk's panic hook (473, 474), down to `panic_utf8`

`env::setup_panic_hook` (522, `SetupPanicHook.lean`) leaves the hook `(1, 1055136)` in the static
cells 1074924/1074928. `rust_panic_with_hook` (824) calls it through the vtable's word at
`1055136 + 12`, the table index 118, whose entry is 473:

```wat
;; 473 <F as Fn>::call(self, info)          ;; the closure is a ZST: `self` unused
local.get 1  call 474  unreachable

;; 474 near_sdk::env::panic_hook_impl(info)
sp -= 32
call 470(sp + 16, info)                     ;; info.to_string(): the String (ptr, cap, len) at sp + 16
call 511(sp + 8, sp + 16)                   ;; String::as_str: (ptr, len) at sp + 8
call 521([sp + 8], [sp + 12])               ;; env::panic_str(ptr, len): panic_utf8, a trap
unreachable

;; 511 as_str(out, s)
sp -= 16;  call 779(sp + 8, s);  [out] := [sp + 8];  [out + 4] := [sp + 12];  sp += 16

;; 779 deref(out, s):  [out + 4] := [s + 8];  [out] := [s]
```

So the hook's message is exactly the bytes `info.to_string()` writes, `<PanicInfo as Display>`.
`f474_spec` is parametric in `to_string`'s specification (`ToStr`): any `MFunSpec` of 470 that
leaves a `String` holding the bytes `bs` at `sp + 16`. It traps with `panicked Cg h bs`
(`PanicStr`): the host's last error `GuestPanic (utf8String bs)`.

* `f779_w`: 779 on words, 8 `regular_op_cost`s;
* `f511_spec`: 511, 39 `regular_op_cost`s (779 included);
* `f474_spec`: 474, `cost474 K bs h` (the closed amount, 285 `regular_op_cost`s, `to_string`'s `K` and `panic_utf8`'s
  `panicUtf8Use h bs.length`);
* `f473_spec`: 473, 11 more (474's activation included).

The stack: 474's frame is `[sp - 32, sp)`; `to_string` runs below `s = sp - 32` within `S ≥ 32`
bytes; 511 and 521 use `[s - 16, s)`, `LocalKey::with` (448) `[s - 32, s - 16)`.
-/

namespace WNear.Binary.PanicHook

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface
open WNear.Binary.PanicStr (panicSlot panicCode panicked mwpi_callT')
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
open WNear.Binary.RegisterLen (frame4)

section Words

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Four bytes of the stack are a word. -/
theorem stk4_word (n a : Nat) : stk (GF := GF) n a 4 ⊢ ∃ w : UInt32, n ↦[i32][ a ] w := by
  iintro H
  iunfold stk at H
  icases H with ⟨%bs, %hbs, H⟩
  iexists UInt32.ofNat (Memory.decodeLE bs)
  rw [ResultExpect.bytes32_decode bs hbs]
  iexact H

/-- `stk_split` at a size given as a sum. -/
theorem stk_split' (n a k k1 k2 : Nat) (h : k = k1 + k2) :
    stk (GF := GF) n a k ⊢ stk n a k1 ∗ stk n (a + k1) k2 := by
  subst h; exact stk_split n a k1 k2

/-- Sixteen bytes of the stack are four words. -/
theorem stk16_frame4 (n : Nat) (fp : UInt32) :
    stk (GF := GF) n fp.toNat 16 ⊢ ∃ w0 w4 w8 w12, frame4 n fp w0 w4 w8 w12 := by
  iintro H
  icases VecFromElem.stk16 n fp.toNat $$ H with ⟨W0, W4, W8, W12⟩
  icases stk4_word n _ $$ W0 with ⟨%w0, W0⟩
  icases stk4_word n _ $$ W4 with ⟨%w4, W4⟩
  icases stk4_word n _ $$ W8 with ⟨%w8, W8⟩
  icases stk4_word n _ $$ W12 with ⟨%w12, W12⟩
  iexists w0, w4, w8, w12
  iunfold frame4
  iframe W0 W4 W8 W12

end Words

/-! ## `deref` (779) and `as_str` (511) -/

section AsStr

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `deref(out, s)` on words: the `String` `(ptr, _, len)` at `s`, two words at `out`. -/
def derefPre (n : Nat) (out s ptr len o0 o4 : UInt32) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 s]⌝ ∗ n ↦[i32][ out.toNat ] o0 ∗ n ↦[i32][ out.toNat + 4 ] o4 ∗
    n ↦[i32][ s.toNat ] ptr ∗ n ↦[i32][ s.toNat + 8 ] len)

def derefPost (n : Nat) (out s ptr len : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] ptr ∗ n ↦[i32][ out.toNat + 4 ] len ∗
    n ↦[i32][ s.toNat ] ptr ∗ n ↦[i32][ s.toNat + 8 ] len)

/-- **`<String as Deref>::deref`** (779) on words: `(ptr, len)` at `out`. -/
theorem f779_w (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out s ptr len o0 o4 : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f779 Cg (derefPre n out s ptr len o0 o4)
      (fun _ => 8 * cfg.regularOpCost) (derefPost n out s ptr len) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold derefPre at HP
  icases HP with ⟨%hargs, O0, O4, S0, S8⟩
  subst hargs
  simp only [f779]
  mstep; mstep; mstep [S8]; mstep [O4]
  mstep; mstep; mstep [S0]; mstep [O0]
  iframe Hc
  iunfold derefPost
  iframe O0 O4 S0 S8
  ipureintro; rfl

/-- `as_str(out, s)`: the stack pointer, 511's frame (two words at `(sp - 16) + 8`), the
`String` at `s`, two words at `out`. -/
def asStrPre (n g : Nat) (gt : GlobalType) (sp out s ptr len o0 o4 a b : UInt32) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i32 s]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ (sp - 16).toNat + 8 ] a ∗
    n ↦[i32][ (sp - 16).toNat + 12 ] b ∗ n ↦[i32][ out.toNat ] o0 ∗ n ↦[i32][ out.toNat + 4 ] o4 ∗
    n ↦[i32][ s.toNat ] ptr ∗ n ↦[i32][ s.toNat + 8 ] len)

def asStrPost (n g : Nat) (gt : GlobalType) (sp out s ptr len : UInt32) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ (sp - 16).toNat + 8 ] ptr ∗
    n ↦[i32][ (sp - 16).toNat + 12 ] len ∗ n ↦[i32][ out.toNat ] ptr ∗ n ↦[i32][ out.toNat + 4 ] len ∗
    n ↦[i32][ s.toNat ] ptr ∗ n ↦[i32][ s.toNat + 8 ] len)

/-- **`String::as_str`** (511): `(ptr, len)` at `out`. -/
theorem f511_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp out s ptr len o0 o4 a b : UInt32) (hsp : 16 ≤ sp.toNat) :
    inst ↪[inst] mi ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f511 Cg (asStrPre n g gt sp out s ptr len o0 o4 a b)
      (fun _ => 39 * cfg.regularOpCost) (asStrPost n g gt sp out s ptr len) := by
  iintro ⟨#Hi, #F779⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have ha779 := hm.funcs 779 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold asStrPre at HP
  icases HP with ⟨%hargs, Hg, A8, A12, O0, O4, S0, S8⟩
  subst hargs
  simp only [f511]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (f779_w cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (sp - 16 + 8) s ptr len a b)
    using [A8 A12 S0 S8]
  · iunfold derefPre
    rw [e8]
    iframe A8 A12 S0 S8
    ipureintro; rfl
  iunfold derefPost at HQ
  icases HQ with ⟨%hrs, A8, A12, S0, S8⟩
  subst hrs
  rw [e8]
  mstep; mstep; mstep [A8]; mstep [O0]
  mstep; mstep; mstep [A12]; mstep [O4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  iframe Hc
  iunfold asStrPost
  iframe Hg A8 A12 O0 O4 S0 S8
  ipureintro; rfl

end AsStr

/-! ## `panic_hook_impl` (474) -/

section Hook

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **What `info.to_string()` (470) is asked**: called with the stack pointer `s`, on the
`PanicInfo` at `ip` and the resources `D`, within `S` bytes of stack below `s`, it writes into the
12 bytes at `s + 16` a `String` `(ptr, cap, len)` holding the bytes `bs`, at the cost `K`. -/
def ToStr (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (s ip : UInt32) (S : Nat) (D : IProp GF) (K : Nat) (bs : List UInt8) :
    IProp GF :=
  MFunSpec cfg lim d types[14]! inst mi f470 Cg
    (fun args => iprop(⌜args = [.i32 (s + 16), .i32 ip]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - S) S ∗ stk n (s.toNat + 16) 12 ∗ D))
    (fun _ => K)
    (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - S) S ∗
      ∃ ptr cap : UInt32, n ↦[i32][ s.toNat + 16 ] ptr ∗ n ↦[i32][ s.toNat + 20 ] cap ∗
        n ↦[i32][ s.toNat + 24 ] UInt32.ofNat bs.length ∗ n ↦[wms][ ptr.toNat ] bs))

instance (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (s ip : UInt32) (S : Nat) (D : IProp GF) (K : Nat) (bs : List UInt8) :
    Persistent (ToStr cfg lim d inst mi Cg n g gt s ip S D K bs) := by
  unfold ToStr; infer_instance

/-- The code 474 runs (persistent). -/
def hookCode (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(A 470 ↪[wf] FuncInst.wasm types[14]! inst f470 ∗ A 511 ↪[wf] FuncInst.wasm types[14]! inst f511 ∗
    A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 521 ↪[wf] FuncInst.wasm types[14]! inst f521 ∗
    A 448 ↪[wf] FuncInst.wasm types[14]! inst f448 ∗ ifaceCode e inst mi A n mx ∗ panicCode e inst mi A)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (hookCode (GF := GF) e inst mi A n mx) := by
  unfold hookCode; infer_instance

/-- 474's precondition: the `PanicInfo` pointer, the stack pointer and `32 + S` bytes below it,
the interface and the `panic_utf8` slot, `to_string`'s resources `D` and the host. -/
def hookPre (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (sp ip : UInt32) (S : Nat) (D : IProp GF)
    (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 ip]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 32 - S) (S + 32) ∗
    iface n ta A ∗ panicSlot n ta A ∗ D ∗ mhostPt h)

/-- 474's cost: `to_string`'s `K`, the rest closed, and `panic_utf8`'s. -/
def cost474 (cfg : WasmConfig) (K : Nat) (bs : List UInt8) (h : NearState) : Nat :=
  285 * cfg.regularOpCost + K + panicUtf8Use h bs.length

theorem stk_hook (n : Nat) (sp : UInt32) (S : Nat) (hS : 32 ≤ S) (hsp : S + 32 ≤ sp.toNat) :
    stk (GF := GF) n (sp.toNat - 32 - S) (S + 32) ⊢
      stk n ((sp - 32).toNat - S) S ∗ stk n (sp - 32).toNat 8 ∗ stk n ((sp - 32).toNat + 8) 8 ∗
        stk n ((sp - 32).toNat + 16) 12 ∗ stk n ((sp - 32).toNat + 28) 4 := by
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iintro H
  icases stk_split n _ S 32 $$ H with ⟨H1, H⟩
  icases stk_split n _ 8 24 $$ H with ⟨H2, H⟩
  icases stk_split n _ 8 16 $$ H with ⟨H3, H⟩
  icases stk_split n _ 12 4 $$ H with ⟨H4, H5⟩
  rw [h32]
  iframe H1
  isplitl [H2]
  · iapply stk_addr _ $$ H2; omega
  isplitl [H3]
  · iapply stk_addr _ $$ H3; omega
  isplitl [H4]
  · iapply stk_addr _ $$ H4; omega
  iapply stk_addr _ $$ H5; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`near_sdk::env::panic_hook_impl(info)`** (474): `info.to_string()` (`ToStr`, the bytes
`bs`), then `env::panic_str` on them: a trap, the host panicked with `bs`. -/
theorem f474_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp ip : UInt32) (S : Nat) (hS : 32 ≤ S) (hsp : S + 32 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (D : IProp GF) (K : Nat) (bs : List UInt8) (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 32)
    (hutf : validUtf8 bs = true) (h : NearState) (hfit : LogFits h bs.length)
    (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    hookCode e inst mi A n mx ∗ ToStr cfg lim (d + 1) inst mi Cg n g gt (sp - 32) ip S D K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f474 Cg (hookPre n g ta A gt sp ip S D h)
        (fun _ => cost474 cfg K bs h) (fun _ _ => iprop(False)) (fun _ => panicked Cg h bs) := by
  iintro ⟨#Hcode, #Hts⟩
  iunfold hookCode at Hcode
  icases Hcode with ⟨#F470, #F511, #F779, #F521, #F448, #Hic, #Hpc⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode at Hpc
    icases Hpc with ⟨-, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (sp - 32 + 16).toNat = (sp - 32).toNat + 16 := by simp [UInt32.toNat_add]; omega
  have e8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have ha470 := hm.funcs 470 (by decide)
  have ha511 := hm.funcs 511 (by decide)
  have ha521 := hm.funcs 521 (by decide)
  iunfold ToStr at Hts
  have t14 : types[14]!.params.length = 2 := by rfl
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold hookPre at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, HS, HD, Hh⟩
  subst hargs
  icases stk_hook n sp S hS hsp $$ Hs with ⟨Hlo, -, H8, Hstr, -⟩
  simp only [f474, cost474]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  -- `info.to_string()`
  mcall Hts using [Hg Hlo Hstr HD]
  · iframe Hg Hlo HD Hstr
  icases HQ with ⟨%hrs, Hg, Hlo, %ptr, %cap, Q16, Q20, Q24, Hb⟩
  subst hrs
  -- `as_str`
  icases stk_split n _ 4 4 $$ H8 with ⟨H8, H12⟩
  icases stk4_word n _ $$ H8 with ⟨%o0, H8⟩
  icases stk4_word n _ $$ H12 with ⟨%o4, H12⟩
  icases stk_split' n _ S (S - 16) 16 (by omega) $$ Hlo with ⟨Hlo, Hf⟩
  icases stk_split n _ 8 8 $$ Hf with ⟨Hf0, Hf8⟩
  icases stk_split n _ 4 4 $$ Hf8 with ⟨Ha, Hb'⟩
  icases stk4_word n _ $$ Ha with ⟨%a, Ha⟩
  icases stk4_word n _ $$ Hb' with ⟨%b, Hb'⟩
  have hs16 : (sp - 32 - 16).toNat = (sp - 32).toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f511_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (sp - 32)
      (sp - 32 + 8) (sp - 32 + 16) ptr (UInt32.ofNat bs.length) o0 o4 a b (by omega))
    using [Hg Ha Hb' H8 H12 Q16 Q24]
  · iunfold asStrPre
    rw [hs16, e8, e16]
    isplitr
    · ipureintro; rfl
    iframe Hg
    isplitl [Ha]
    · iapply memBytes_congr (by omega) |>.1 $$ Ha
    isplitl [Hb']
    · iapply memBytes_congr (by omega) |>.1 $$ Hb'
    isplitl [H8]
    · iexact H8
    isplitl [H12]
    · iapply memBytes_congr (by omega) |>.1 $$ H12
    isplitl [Q16]
    · iexact Q16
    iapply memBytes_congr (by omega) |>.1 $$ Q24
  iunfold asStrPost at HQ
  icases HQ with ⟨%hrs, Hg, Ha, Hb', H8, H12, Q16, Q24⟩
  subst hrs
  rw [e8] at *
  -- `env::panic_str(ptr, len)`
  mstep; mstep [H8]
  mstep; mstep [H12]
  have hL : (UInt32.ofNat bs.length).toNat = bs.length := by
    simp only [UInt32.toNat_ofNat']; omega
  icases stk_split' n _ (S - 16) (S - 32) 16 (by omega) $$ Hlo with ⟨-, Hfr⟩
  have h64 : (sp - 32 - 16 - 16).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, hs16, h32] <;> omega
  ihave Hfr := stk_addr (show (sp - 32).toNat - S + (S - 32) = (sp - 32 - 16 - 16).toNat by omega) $$ Hfr
  icases stk16_frame4 n _ $$ Hfr with ⟨%w0, %w4, %w8, %w12, Hfr⟩
  iapply mwpi_cons
  iapply mwpi_callT' (i := 521) (a := A 521) (type := types[14]!) (inst := inst) (mi := mi)
    (code := f521) [.i32 ptr, .i32 (UInt32.ofNat bs.length)]
  isplitr
  · iapply (PanicStr.f521_spec cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg
      { type := gt, value := .i32 (sp - 32) } (sp - 32) rfl (by omega) (by omega) ptr
      (UInt32.ofNat bs.length) bs hL.symm (by omega) hutf ptr (UInt32.ofNat bs.length) w0 w4 w8 w12 h
      (by rw [hL]; exact hfit) (by rw [hL]; exact hov))
    iframe F448 Hic Hpc
  isplitr
  · iexact F521
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha521, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; rw [hL]; omega
  isplitl [Hg HI HS Ha Hb' Hfr Hb Hh]
  · iunfold PanicStr.pre
    iframe Hg HI HS Ha Hb' Hfr Hb Hh
    ipureintro; rfl
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

/-- **`<F as Fn>::call`** (473), the hook's vtable entry: `panic_hook_impl(info)` (474). -/
theorem f473_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp self ip : UInt32) (S : Nat) (hS : 32 ≤ S) (hsp : S + 32 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (D : IProp GF) (K : Nat) (bs : List UInt8) (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 32)
    (hutf : validUtf8 bs = true) (h : NearState) (hfit : LogFits h bs.length)
    (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    A 474 ↪[wf] FuncInst.wasm types[0]! inst f474 ∗ hookCode e inst mi A n mx ∗
      ToStr cfg lim (d + 2) inst mi Cg n g gt (sp - 32) ip S D K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f473 Cg
        (fun args => iprop(⌜args = [.i32 self, .i32 ip]⌝ ∗ hookPre n g ta A gt sp ip S D h [.i32 ip]))
        (fun _ => 11 * cfg.regularOpCost + cost474 cfg K bs h) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h bs) := by
  iintro ⟨#F474, #Hcode, #Hts⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold hookCode, panicCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha474 := hm.funcs 474 (by decide)
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f473]
  mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 474) (a := A 474) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f474) [.i32 ip]
  isplitr
  · iapply (f474_spec cfg lim (d + 1) types[0]! inst mi e A n g ta mx hm (by omega) Cg gt sp ip S hS hsp
      hal D K bs hpos hlen hutf h hfit hov)
    iframe Hcode Hts
  isplitr
  · iexact F474
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha474, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [HP]
  · iexact HP
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

end Hook

end WNear.Binary.PanicHook
