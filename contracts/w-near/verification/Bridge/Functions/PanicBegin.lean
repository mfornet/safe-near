import Bridge.Functions.PanicWithHook
import Binary.Code.Part12
import Binary.Code.Part18

/-!
# `std::panicking::begin_panic::<&str>` (664), down to the hook's trap

`panic!("literal")`, `assert!(c, "literal")` and `require!(c, "literal")` (near-sdk 3.1's
`require!` is `assert!`) compile to `begin_panic(msg_ptr, msg_len, &LOCATION)` (664):

```wat
;; 664 begin_panic(m, l, loc)
sp -= 16;  [sp+8] := 888(loc) = loc;  [sp+4] := l;  [sp] := m      ;; Location::caller is the identity
call 662(sp)                                         ;; __rust_end_short_backtrace(&(msg, loc))
;; 662 (p)
sp -= 16;  [sp+8] := [p+8];  [sp..8] := [p..8];  call 663(sp)
;; 663 begin_panic::{{closure}}(p)
sp -= 16;  [sp+8..16] := [p..8]                      ;; PanicPayload { inner: Some(msg) }
call 824(sp + 8, 1062968, 0, [p+8])                  ;; rust_panic_with_hook(&mut payload, None, loc)
;; 679 <PanicPayload<&str> as BoxMeUp>::get(out, p0)     (the vtable 1062968's slot 16: table 137)
[p0] = 0 ⇒ abort (815);  [out+4] := 1062988;  [out] := p0  ;; &(dyn Any) of the &str
```

The message is `None`: the hook's `Display for PanicInfo` takes the payload's `&str` (its
`type_id`, 661 through the vtable 1062988, is the constant 9147559743429524724 of `&str`).

`f664_spec`: from the stack pointer `sp`, with `S + 112` bytes below it, the hook installed and the
`get` slot, the message `(m, l)` (`m ≠ 0`, any static string) and the location `loc`: it traps,
the host panicked with the bytes `bs` `to_string` writes on the `PanicInfo`
`(payload (sp - 40, 1062988), message None, location loc)`, the payload's `&str` `(m, l)` at
`sp - 40` (`payloadCells`). `to_string`'s specification (`ToStr`) is a premise.

Costs (`regular_op_cost`s, the callees' activations included): 664 `36`, 662 `28`, 663 `28`, 679 `9`, then 824
(`cost824` with 679's `9`): in all `cost664 K bs h`.
-/

namespace WNear.Binary.PanicBegin

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface
open WNear.Binary.PanicStr (panicSlot panicCode panicked mwpi_callT')
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
open WNear.Binary.PanicHook (ToStr hookCode cost474 stk4_word stk_split')
open WNear.Binary.PanicWithHook (hookInstalled infoCells GetSpec cost824)

/-! ## The data -/

/-- The payload vtable 1062968 (`PanicPayload<&str>`): `get` at the table index 137. -/
theorem vtable_get : dataWord (1062968 + 16) = bytes32 137 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entry 137: 679. -/
theorem wTable_get : wTable.elems[137]? = some (Ref.func 679) := rfl

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## `Location::caller` (888) and the payload's `get` (679) -/

/-- **`Location::caller`** (888) under `#[track_caller]`: its argument. -/
theorem f888_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (loc : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f888 Cg (fun args => iprop(⌜args = [.i32 loc]⌝))
      (fun _ => cfg.regularOpCost) (fun _ rs => iprop(⌜rs = [.i32 loc]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f888]
  mstep
  iframe Hc
  ipureintro; rw [htype]; rfl

/-- The payload `PanicPayload { inner: Some((m, l)) }` at `p0`. -/
def payloadCells (n : Nat) (p0 m l : UInt32) : IProp GF :=
  iprop(n ↦[i32][ p0.toNat ] m ∗ n ↦[i32][ p0.toNat + 4 ] l)

/-- **`<PanicPayload<&str> as BoxMeUp>::get`** (679) on `Some`: the `&dyn Any` `(p0, 1062988)`. -/
theorem f679_get (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (gt : GlobalType) (s p0 m l : UInt32) (hm0 : m ≠ 0) (S : Nat)
    (hs : s.toNat + 16 ≤ 2 ^ 32) :
    ⊢ GetSpec (GF := GF) cfg lim d inst mi Cg n g gt s p0 p0 1062988 S f679
        (payloadCells n p0 m l) (payloadCells n p0 m l) (9 * cfg.regularOpCost) := by
  iunfold GetSpec
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, H8, HP⟩
  subst hargs
  iunfold payloadCells at HP
  icases HP with ⟨M0, M4⟩
  have e8 : (s + 8).toNat = s.toNat + 8 := by simp [UInt32.toNat_add]; omega
  icases stk_split n _ 4 4 $$ H8 with ⟨O0, O4⟩
  icases stk4_word n _ $$ O0 with ⟨%o0, O0⟩
  icases stk4_word n _ $$ O4 with ⟨%o4, O4⟩
  ihave O0 := memBytes_congr (j := (s + 8).toNat) (by omega) |>.1 $$ O0
  ihave O4 := memBytes_congr (j := (s + 8).toNat + 4) (by omega) |>.1 $$ O4
  simp only [f679]
  mstep
  mstep; mstep [M0]
  mstep_taken with (simp [hm0])
  mstep; mstep; mstep [O4]
  mstep; mstep; mstep [O0]
  iframe Hc Hg Hs
  rw [e8]
  iframe O0 O4
  iunfold payloadCells
  iframe M0 M4

/-! ## `begin_panic::{{closure}}` (663) -/

/-- The code the panic runs (persistent): 824, the payload's `get` (679), the hook. -/
def panicCode' (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(A 824 ↪[wf] FuncInst.wasm types[45]! inst f824 ∗ A 679 ↪[wf] FuncInst.wasm types[14]! inst f679 ∗
    A 473 ↪[wf] FuncInst.wasm types[14]! inst f473 ∗ A 474 ↪[wf] FuncInst.wasm types[0]! inst f474 ∗
    hookCode e inst mi A n mx)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (panicCode' (GF := GF) e inst mi A n mx) := by
  unfold panicCode'; infer_instance

/-- What every layer passes down: the hook installed with its `get` slot for `PanicPayload<&str>`,
the resources `D0`, the interface, the `panic_utf8` slot and the host. -/
def env (n ta : Nat) (A : Nat → Nat) (lpc : UInt32) (D0 : IProp GF) (h : NearState) : IProp GF :=
  iprop(hookInstalled n ta A lpc ∗ n ↦[i32][ 1062968 + 16 ] 137 ∗ ta ↦[wt][ 137 ] Ref.func (A 679) ∗
    D0 ∗ iface n ta A ∗ panicSlot n ta A ∗ mhostPt h)

/-- The `PanicInfo` and the payload `to_string` sees, from 824's stack pointer `s` on the payload
at `p0`. -/
def infoD (n : Nat) (s p0 m l loc : UInt32) (D0 : IProp GF) : IProp GF :=
  iprop(infoCells n (s - 32 + 16) p0 1062988 0 loc ∗ payloadCells n p0 m l ∗ D0)

/-- 663's cost. -/
noncomputable def cost663 (cfg : WasmConfig) (K : Nat) (bs : List UInt8) (h : NearState) : Nat :=
  28 * cfg.regularOpCost + cost824 cfg f679 (9 * cfg.regularOpCost) K bs h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`begin_panic::{{closure}}`** (663) on `p`, the message `(m, l)` and the location `loc`. -/
theorem f663_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp p m l loc lpc : UInt32) (hm0 : m ≠ 0) (S : Nat) (hS : 32 ≤ S) (hsp : S + 80 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (D0 : IProp GF) (K : Nat) (bs : List UInt8) (hpos : 0 < bs.length)
    (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hfit : LogFits h bs.length) (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    panicCode' e inst mi A n mx ∗
      ToStr cfg lim (d + 4) inst mi Cg n g gt (sp - 16 - 32 - 32) (sp - 16 - 32 + 16) S
        (infoD n (sp - 16) (sp - 16 + 8) m l loc D0) K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f663 Cg
        (fun args => iprop(⌜args = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 80 - S) (S + 80) ∗
          n ↦[i32][ p.toNat ] m ∗ n ↦[i32][ p.toNat + 4 ] l ∗ n ↦[i32][ p.toNat + 8 ] loc ∗
          env n ta A lpc D0 h))
        (fun _ => cost663 cfg K bs h) (fun _ _ => iprop(False)) (fun _ => panicked Cg h bs) := by
  iintro ⟨#Hc', #Hts⟩
  iunfold panicCode' at Hc'
  icases Hc' with ⟨#F824, #F679, #F473, #F474, #Hcode⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold hookCode, panicCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have ha824 := hm.funcs 824 (by decide)
  have h48 : (sp - 16 - 32).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h16] <;> omega
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, M, L, Lc, HE⟩
  subst hargs
  iunfold env at HE
  icases HE with ⟨HH, V137, T137, HD0, HI, HS, Hh⟩
  icases stk_split' n _ (S + 80) (S + 64) 16 (by omega) $$ Hs with ⟨Hlo, Hf⟩
  icases stk_split n _ 8 8 $$ Hf with ⟨-, Hf8⟩
  ihave Hf8 := stk_addr (show sp.toNat - 80 - S + (S + 64) + 8 = (sp - 16).toNat + 8 by omega) $$ Hf8
  iunfold stk at Hf8
  icases Hf8 with ⟨%ob, %hob, Hf8⟩
  ihave ML := (memBytes_append n p.toNat (bytes32 m) (bytes32 l)).2 $$ [M L]
  · isplitl [M]
    · iexact M
    iapply memBytes_congr (by simp) |>.1 $$ L
  simp only [f663, cost663]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [ML]; mstep [Hf8]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  icases (memBytes_append n ((sp - 16).toNat + 8) (bytes32 m) (bytes32 l)).1 $$ Hf8 with ⟨P0, P4⟩
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [Lc]
  iapply mwpi_cons
  iapply mwpi_callT' (i := 824) (a := A 824) (type := types[45]!) (inst := inst) (mi := mi)
    (code := f824) [.i32 (sp - 16 + 8), .i32 1062968, .i32 0, .i32 loc]
  isplitr
  · iapply (PanicWithHook.f824_spec cfg lim (d + 1) types[45]! inst mi e A n g ta mx hm (by omega) Cg gt
      (sp - 16) (sp - 16 + 8) 1062968 0 loc 137 (A 679) f679 (sp - 16 + 8) 1062988 lpc S hS (by omega)
      (by omega) (by decide) (payloadCells n (sp - 16 + 8) m l) (payloadCells n (sp - 16 + 8) m l) D0
      (9 * cfg.regularOpCost) K bs hpos hlen hutf h hfit hov)
    iframe F679 F473 F474 Hcode
    isplitr
    · iapply f679_get cfg lim (d + 2) inst mi Cg n g hn gt (sp - 16 - 32) (sp - 16 + 8) m l hm0 (S + 32)
        (by omega)
    iunfold infoD at Hts
    iexact Hts
  isplitr
  · iexact F824
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha824, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Hlo HH V137 T137 HD0 HI HS Hh P0 P4]
  · iunfold PanicWithHook.pre
    iframe Hg HH HD0 HI HS Hh
    isplitr
    · ipureintro; rfl
    isplitl [Hlo]
    · iapply stk_addr _ $$ Hlo; omega
    simp only [UInt32.reduceToNat]
    isplitl [V137]
    · iexact V137
    isplitl [T137]
    · iexact T137
    iunfold payloadCells
    rw [e8]
    iframe P0
    iapply memBytes_congr (by simp) |>.1 $$ P4
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

/-! ## `__rust_end_short_backtrace` (662) and `begin_panic` (664) -/

/-- 662's cost. -/
noncomputable def cost662 (cfg : WasmConfig) (K : Nat) (bs : List UInt8) (h : NearState) : Nat :=
  28 * cfg.regularOpCost + cost663 cfg K bs h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`__rust_end_short_backtrace`** (662) on `p`: the message and the location copied, 663. -/
theorem f662_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp p m l loc lpc : UInt32) (hp : p.toNat + 12 ≤ 2 ^ 32) (hm0 : m ≠ 0) (S : Nat) (hS : 32 ≤ S)
    (hsp : S + 96 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (D0 : IProp GF) (K : Nat) (bs : List UInt8) (hpos : 0 < bs.length)
    (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hfit : LogFits h bs.length) (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    A 663 ↪[wf] FuncInst.wasm types[0]! inst f663 ∗ panicCode' e inst mi A n mx ∗
      ToStr cfg lim (d + 5) inst mi Cg n g gt (sp - 16 - 16 - 32 - 32) (sp - 16 - 16 - 32 + 16) S
        (infoD n (sp - 16 - 16) (sp - 16 - 16 + 8) m l loc D0) K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f662 Cg
        (fun args => iprop(⌜args = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96 - S) (S + 96) ∗
          n ↦[i32][ p.toNat ] m ∗ n ↦[i32][ p.toNat + 4 ] l ∗ n ↦[i32][ p.toNat + 8 ] loc ∗
          env n ta A lpc D0 h))
        (fun _ => cost662 cfg K bs h) (fun _ _ => iprop(False)) (fun _ => panicked Cg h bs) := by
  iintro ⟨#F663, #Hc', #Hts⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode', hookCode, panicCode at Hc'
    icases Hc' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have ha663 := hm.funcs 663 (by decide)
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, M, L, Lc, HE⟩
  subst hargs
  icases stk_split' n _ (S + 96) (S + 80) 16 (by omega) $$ Hs with ⟨Hlo, Hf⟩
  icases stk_split n _ 8 8 $$ Hf with ⟨Hf0, Hf8⟩
  ihave Hf0 := stk_addr (show sp.toNat - 96 - S + (S + 80) = (sp - 16).toNat by omega) $$ Hf0
  ihave Hf8 := stk_addr (show sp.toNat - 96 - S + (S + 80) + 8 = (sp - 16).toNat + 8 by omega) $$ Hf8
  icases stk_split n _ 4 4 $$ Hf8 with ⟨Hf8, -⟩
  icases stk4_word n _ $$ Hf8 with ⟨%w8, Hf8⟩
  ihave Hf8 := memBytes_congr (j := (sp - 16 + 8).toNat) (by omega) |>.1 $$ Hf8
  iunfold stk at Hf0
  icases Hf0 with ⟨%ob, %hob, Hf0⟩
  ihave ML := (memBytes_append n p.toNat (bytes32 m) (bytes32 l)).2 $$ [M L]
  · isplitl [M]
    · iexact M
    iapply memBytes_congr (by simp) |>.1 $$ L
  simp only [f662, cost662]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [Lc]; mstep [Hf8]
  mstep; mstep; mstep [ML]; mstep [Hf0]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  icases (memBytes_append n (sp - 16).toNat (bytes32 m) (bytes32 l)).1 $$ Hf0 with ⟨P0, P4⟩
  mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 663) (a := A 663) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f663) [.i32 (sp - 16)]
  isplitr
  · iapply (f663_spec cfg lim (d + 1) types[0]! inst mi e A n g ta mx hm (by omega) Cg gt (sp - 16)
      (sp - 16) m l loc lpc hm0 S hS (by omega) (by omega) D0 K bs hpos hlen hutf h hfit hov)
    iframe Hc' Hts
  isplitr
  · iexact F663
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha663, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Hlo P0 P4 Hf8 HE]
  · iframe Hg HE P0
    isplitr
    · ipureintro; rfl
    isplitl [Hlo]
    · iapply stk_addr _ $$ Hlo; omega
    isplitl [P4]
    · iapply memBytes_congr (by simp) |>.1 $$ P4
    iapply memBytes_congr (by omega) |>.1 $$ Hf8
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

/-- 664's cost. -/
noncomputable def cost664 (cfg : WasmConfig) (K : Nat) (bs : List UInt8) (h : NearState) : Nat :=
  36 * cfg.regularOpCost + cost662 cfg K bs h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`std::panicking::begin_panic::<&str>(m, l, loc)`** (664): `panic!` with the static message
`(m, l)` at the location `loc`. With the near-sdk hook installed, no panic in progress and the
`get` slot of the payload vtable, it traps, the host panicked with the bytes `to_string` writes on
the `PanicInfo` (payload the `&str` `(m, l)`, message `None`, location `loc`). -/
theorem f664_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp m l loc lpc : UInt32) (hm0 : m ≠ 0) (S : Nat) (hS : 32 ≤ S) (hsp : S + 112 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (D0 : IProp GF) (K : Nat) (bs : List UInt8) (hpos : 0 < bs.length)
    (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hfit : LogFits h bs.length) (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    A 662 ↪[wf] FuncInst.wasm types[0]! inst f662 ∗ A 663 ↪[wf] FuncInst.wasm types[0]! inst f663 ∗
      A 888 ↪[wf] FuncInst.wasm types[32]! inst f888 ∗ panicCode' e inst mi A n mx ∗
      ToStr cfg lim (d + 6) inst mi Cg n g gt (sp - 16 - 16 - 16 - 32 - 32) (sp - 16 - 16 - 16 - 32 + 16) S
        (infoD n (sp - 16 - 16 - 16) (sp - 16 - 16 - 16 + 8) m l loc D0) K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f664 Cg
        (fun args => iprop(⌜args = [.i32 m, .i32 l, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 112 - S) (S + 112) ∗ env n ta A lpc D0 h))
        (fun _ => cost664 cfg K bs h) (fun _ _ => iprop(False)) (fun _ => panicked Cg h bs) := by
  iintro ⟨#F662, #F663, #F888, #Hc', #Hts⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold panicCode', hookCode, panicCode at Hc'
    icases Hc' with ⟨-, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have ha662 := hm.funcs 662 (by decide)
  have ha888 := hm.funcs 888 (by decide)
  have t32 : types[32]!.params.length = 1 := by rfl
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HE⟩
  subst hargs
  icases stk_split' n _ (S + 112) (S + 96) 16 (by omega) $$ Hs with ⟨Hlo, Hf⟩
  ihave Hf := stk_addr (show sp.toNat - 112 - S + (S + 96) = (sp - 16).toNat by omega) $$ Hf
  icases VecFromElem.stk16 n _ $$ Hf with ⟨W0, W4, W8, -⟩
  icases stk4_word n _ $$ W0 with ⟨%w0, W0⟩
  icases stk4_word n _ $$ W4 with ⟨%w4, W4⟩
  icases stk4_word n _ $$ W8 with ⟨%w8, W8⟩
  simp only [f664, cost664]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mcall (f888_spec cfg lim (d + 1) types[32]! (by rfl) inst mi Cg loc) using []
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep [W8]
  mstep; mstep; mstep [W4]
  mstep; mstep; mstep [W0]
  mstep
  iapply mwpi_cons
  iapply mwpi_callT' (i := 662) (a := A 662) (type := types[0]!) (inst := inst) (mi := mi)
    (code := f662) [.i32 (sp - 16)]
  isplitr
  · iapply (f662_spec cfg lim (d + 1) types[0]! inst mi e A n g ta mx hm (by omega) Cg gt (sp - 16)
      (sp - 16) m l loc lpc (by omega) hm0 S hS (by omega) (by omega) D0 K bs hpos hlen hutf h hfit hov)
    iframe F663 Hc' Hts
  isplitr
  · iexact F662
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha662, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Hlo W0 W4 W8 HE]
  · iframe Hg HE W0 W4 W8
    isplitr
    · ipureintro; rfl
    iapply stk_addr _ $$ Hlo; omega
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mfunc]
    iexact HT

end Spec

end WNear.Binary.PanicBegin
