import Bridge.Functions.PanicBegin
import Binary.Code.Part15

/-!
# `core::panicking::panic_fmt` (859) and its entries, down to the hook's trap

`panic_fmt(args, loc)` is the panic of `core`: `expect_failed`, `panic` (the arithmetic overflow
messages), `assert_eq!`, `unreachable!`, `unwrap` on `None`. In this binary (Rust 1.51):

```wat
;; 859 panic_fmt(a, loc)
sp -= 16;  PanicInfo at sp: payload (1067136, 1070656), message a, location loc
call 823(sp)                                        ;; rust_begin_unwind(&info)
;; 823 rust_begin_unwind(info)
sp -= 16;  loc := expect(884(info) = [info+12]);  msg := expect(883(info) = [info+8])   ;; 796, 795
[sp+8] := loc;  [sp+4] := info;  [sp] := msg;  call 816(sp)
;; 816 __rust_end_short_backtrace(p):  sp -= 16;  copy the 12 bytes of p;  call 817(sp)
;; 817 begin_panic_handler::{{closure}}(p):  [p] = msg (&Arguments a), [p+4] = info, [p+8] = loc
sp -= 16
pieces.len = 1 ∧ args.len = 0:  payload StrPanicPayload(pieces[0]) at sp, vtable 1066380
otherwise (args.len ≠ 0, or pieces.len ≥ 2):  payload PanicPayload { inner: a, string: None } at sp,
                                              vtable 1066360
(pieces.len = 0 ∧ args.len = 0: payload "" — not used here)
call 824(sp, vtable, 883([p+4]) = msg, loc)          ;; rust_panic_with_hook(payload, Some(a), loc)
```

* `StrPanicPayload::get` (828, the vtable 1066380's slot 16: table 181): `(p0, 1066416)`, no check;
* `PanicPayload::get` (826, the vtable 1066360's slot 16: table 179) *formats the message into a
  fresh `String`* (`fill`: 872 with the sink 1065680, allocating), although the hook will not
  read it: with `message: Some(a)`, `<PanicInfo as Display>` formats `a` itself.

The layers are generic in the next one: `Spec817` is what 816, 823 and 859 ask of 817, at its stack
pointer, on `(msg, info, loc)` and the resources `E`. `f817_str` and `f817_fmt` prove it for the two
payloads, parametric in the payload's `get` (`GetSpec`) and in `to_string` (`ToStr`).

The entries:

* `core::panicking::panic(m, l, loc)` (853): `Arguments { pieces: [(m, l)], fmt: None, args: [] }`,
  then 859: the `StrPanicPayload` branch (`f853_spec`);
* `core::option::expect_failed(m, l, loc)` (879): `Arguments { pieces: [""] (1070628), fmt: None,
  args: [(&(m, l), 195)] }` — `format_args!("{}", msg)` — then 859: the `PanicPayload` branch
  (`f879_spec`). The hook's message is `panicked at '{}', loc` on `"{}"` of the `&str` `(m, l)`
  (195 is 880, `<&str as Display>`): the expect message itself.
-/

namespace WNear.Binary.PanicFmt

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface
open WNear.Binary.PanicStr (panicSlot panicCode panicked mwpi_callT')
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
open WNear.Binary.PanicHook (ToStr hookCode cost474 stk4_word stk_split')
open WNear.Binary.PanicWithHook (hookInstalled infoCells GetSpec cost824)
open WNear.Binary.PanicBegin (panicCode')

/-! ## The data -/

/-- The `StrPanicPayload` vtable 1066380: `get` at the table index 181. -/
theorem vtable_strGet : dataWord (1066380 + 16) = bytes32 181 := by
  rw [dataWord_eq _ (by decide)]; decide

/-- The `PanicPayload` vtable 1066360: `get` at the table index 179. -/
theorem vtable_fmtGet : dataWord (1066360 + 16) = bytes32 179 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
theorem wTable_strGet : wTable.elems[181]? = some (Ref.func 828) := rfl

set_option maxRecDepth 100000 in
theorem wTable_fmtGet : wTable.elems[179]? = some (Ref.func 826) := rfl

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## The small callees -/

/-- **`StrPanicPayload::get`** (828): the `&dyn Any` `(p0, 1066416)`. -/
theorem f828_get (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (gt : GlobalType) (s p0 : UInt32) (S : Nat)
    (hs : s.toNat + 16 ≤ 2 ^ 32) (G : IProp GF) :
    ⊢ GetSpec (GF := GF) cfg lim d inst mi Cg n g gt s p0 p0 1066416 S f828 G G (6 * cfg.regularOpCost) := by
  iunfold GetSpec
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, H8, HG⟩
  subst hargs
  have e8 : (s + 8).toNat = s.toNat + 8 := by simp [UInt32.toNat_add]; omega
  icases stk_split n _ 4 4 $$ H8 with ⟨O0, O4⟩
  icases stk4_word n _ $$ O0 with ⟨%o0, O0⟩
  icases stk4_word n _ $$ O4 with ⟨%o4, O4⟩
  ihave O0 := memBytes_congr (j := (s + 8).toNat) (by omega) |>.1 $$ O0
  ihave O4 := memBytes_congr (j := (s + 8).toNat + 4) (by omega) |>.1 $$ O4
  simp only [f828]
  mstep; mstep; mstep [O4]
  mstep; mstep; mstep [O0]
  iframe Hc Hg Hs HG
  rw [e8]
  iframe O0 O4

/-- `PanicInfo::message` (883) / `PanicInfo::location` (884): a word of the `PanicInfo`. -/
theorem f883_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (info w : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f883 Cg
      (fun args => iprop(⌜args = [.i32 info]⌝ ∗ n ↦[i32][ info.toNat + 8 ] w)) (fun _ => 2 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 w]⌝ ∗ n ↦[i32][ info.toNat + 8 ] w)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, W⟩ Hc
  subst hargs
  simp only [f883]
  mstep; mstep [W]
  iframe Hc W
  ipureintro; rw [htype]; rfl

theorem f884_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (info w : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f884 Cg
      (fun args => iprop(⌜args = [.i32 info]⌝ ∗ n ↦[i32][ info.toNat + 12 ] w)) (fun _ => 2 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 w]⌝ ∗ n ↦[i32][ info.toNat + 12 ] w)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, W⟩ Hc
  subst hargs
  simp only [f884]
  mstep; mstep [W]
  iframe Hc W
  ipureintro; rw [htype]; rfl

/-- `Option::unwrap` (795) on `Some`: its argument, not zero. -/
theorem f795_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (w : UInt32) (hw : w ≠ 0) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f795 Cg
      (fun args => iprop(⌜args = [.i32 w]⌝)) (fun _ => 3 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 w]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f795]
  mstep; mstep
  mstep_taken with (simp [hw])
  mstep
  iframe Hc
  ipureintro; rw [htype]; rfl

/-- `Option::unwrap` (796, `#[track_caller]`) on `Some`: its argument, not zero. -/
theorem f796_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (w c : UInt32) (hw : w ≠ 0) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f796 Cg
      (fun args => iprop(⌜args = [.i32 w, .i32 c]⌝)) (fun _ => 3 * cfg.regularOpCost)
      (fun _ rs => iprop(⌜rs = [.i32 w]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f796]
  mstep; mstep
  mstep_taken with (simp [hw])
  mstep
  iframe Hc
  ipureintro; rw [htype]; rfl


/-! ## `begin_panic_handler::{{closure}}` (817) -/

/-- **What 816 asks of 817**: at the stack pointer `sp`, on `p` holding `(msg, info, loc)` and the
resources `E`, a trap with the host panicked with `bs`, at the cost `K`. -/
def Spec817 (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (sp p msg info loc : UInt32) (E : IProp GF) (K : Nat) (h : NearState)
    (bs : List UInt8) : IProp GF :=
  MFunSpecT cfg lim d types[0]! inst mi f817 Cg
    (fun args => iprop(⌜args = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ n ↦[i32][ p.toNat ] msg ∗
      n ↦[i32][ p.toNat + 4 ] info ∗ n ↦[i32][ p.toNat + 8 ] loc ∗ E))
    (fun _ => K) (fun _ _ => iprop(False)) (fun _ => panicked Cg h bs)

instance (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (sp p msg info loc : UInt32) (E : IProp GF) (K : Nat) (h : NearState)
    (bs : List UInt8) : Persistent (Spec817 cfg lim d inst mi Cg n g gt sp p msg info loc E K h bs) := by
  unfold Spec817 MFunSpecT; infer_instance

/-- The hook installed and the payload vtable `vt`'s `get` slot (table `gidx`, entry `ag`), the
resources `D0`, the interface, the `panic_utf8` slot and the host. -/
def envP (n ta : Nat) (A : Nat → Nat) (lpc vt gidx : UInt32) (ag : Nat) (D0 : IProp GF) (h : NearState) :
    IProp GF :=
  iprop(hookInstalled n ta A lpc ∗ n ↦[i32][ vt.toNat + 16 ] gidx ∗ ta ↦[wt][ gidx.toNat ] Ref.func ag ∗
    D0 ∗ iface n ta A ∗ panicSlot n ta A ∗ mhostPt h)

/-- What 817 reads of the `Arguments` `a`: its pieces' count and arguments' count. -/
def argsHead (n : Nat) (a plen alen : UInt32) : IProp GF :=
  iprop(n ↦[i32][ a.toNat + 4 ] plen ∗ n ↦[i32][ a.toNat + 20 ] alen)

/-- The code 817 runs (persistent). -/
def code817 (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) : IProp GF :=
  iprop(A 883 ↪[wf] FuncInst.wasm types[32]! inst f883 ∗ A 824 ↪[wf] FuncInst.wasm types[45]! inst f824 ∗
    A 473 ↪[wf] FuncInst.wasm types[14]! inst f473 ∗ A 474 ↪[wf] FuncInst.wasm types[0]! inst f474 ∗
    hookCode e inst mi A n mx)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n : Nat) (mx : Option Nat) :
    Persistent (code817 (GF := GF) e inst mi A n mx) := by
  unfold code817; infer_instance

/-- 817's cost on a payload whose `get` is `codeG` at the cost `Kg`. -/
noncomputable def cost817 (cfg : WasmConfig) (codeG : Func) (Kg K : Nat) (bs : List UInt8) (h : NearState) :
    Nat :=
  61 * cfg.regularOpCost + cost824 cfg codeG Kg K bs h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **817 on one piece and no argument** (`core::panicking::panic`): the payload
`StrPanicPayload((ptr, len))`, the piece; its `get` is 828. -/
theorem f817_str (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (e : Nat)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp p a info loc msg pp ptr len lpc : UInt32) (S : Nat) (hS : 32 ≤ S)
    (hsp : S + 80 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (ha : a.toNat + 24 ≤ 2 ^ 32)
    (hp : p.toNat + 12 ≤ 2 ^ 32) (hinfo : info.toNat + 12 ≤ 2 ^ 32) (hpp : pp.toNat + 8 ≤ 2 ^ 32)
    (D0 : IProp GF) (K : Nat) (bs : List UInt8) (hpos : 0 < bs.length)
    (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hfit : LogFits h bs.length) (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    code817 e inst mi A n mx ∗ A 828 ↪[wf] FuncInst.wasm types[14]! inst f828 ∗
      ToStr cfg lim (d + 4) inst mi Cg n g gt (sp - 16 - 32 - 32) (sp - 16 - 32 + 16) S
        iprop(infoCells n (sp - 16 - 32 + 16) (sp - 16) 1066416 msg loc ∗
          (n ↦[i32][ (sp - 16).toNat ] ptr ∗ n ↦[i32][ (sp - 16).toNat + 4 ] len) ∗
          (n ↦[i32][ info.toNat + 8 ] msg ∗ argsHead n a 1 0 ∗ n ↦[i32][ a.toNat ] pp ∗
            n ↦[i32][ pp.toNat ] ptr ∗ n ↦[i32][ pp.toNat + 4 ] len ∗ D0)) K bs
      ⊢ Spec817 cfg lim d inst mi Cg n g gt sp p a info loc
          iprop(stk n (sp.toNat - 80 - S) (S + 80) ∗ n ↦[i32][ info.toNat + 8 ] msg ∗ argsHead n a 1 0 ∗
            n ↦[i32][ a.toNat ] pp ∗ n ↦[i32][ pp.toNat ] ptr ∗ n ↦[i32][ pp.toNat + 4 ] len ∗
            envP n ta A lpc 1066380 181 (A 828) D0 h)
          (cost817 cfg f828 (6 * cfg.regularOpCost) K bs h) h bs := by
  iintro ⟨#Hc', #F828, #Hts⟩
  iunfold code817 at Hc'
  icases Hc' with ⟨#F883, #F824, #F473, #F474, #Hcode⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold hookCode, panicCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h48 : (sp - 16 - 32).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h16] <;> omega
  have ha824 := hm.funcs 824 (by decide)
  have ha883 := hm.funcs 883 (by decide)
  have t32 : types[32]!.params.length = 1 := by rfl
  iunfold Spec817
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, P0, P4, P8, Hs, HM, HA, A0, Q0, Q4, HE⟩
  subst hargs
  iunfold argsHead at HA
  icases HA with ⟨A4, A20⟩
  iunfold envP at HE
  icases HE with ⟨HH, Vg, Tg, HD0, HI, HS, Hh⟩
  icases stk_split' n _ (S + 80) (S + 64) 16 (by omega) $$ Hs with ⟨Hlo, Hf⟩
  ihave Hf := stk_addr (show sp.toNat - 80 - S + (S + 64) = (sp - 16).toNat by omega) $$ Hf
  icases stk_split n _ 8 8 $$ Hf with ⟨Hf0, Hf8⟩
  icases stk_split n _ 4 4 $$ Hf0 with ⟨W0, W4⟩
  icases stk4_word n _ $$ W0 with ⟨%w0, W0⟩
  icases stk4_word n _ $$ W4 with ⟨%w4, W4⟩
  ihave A20 := memBytes_congr (j := (a + 20).toNat) (by simp [UInt32.toNat_add]; omega) |>.1 $$ A20
  simp only [f817, cost817, cost824]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep [P0]; mstep; mstep; mstep; mstep [A20]; mstep
  mstep; mstep; mstep; mstep
  mstep; mstep [A4]
  mstep
  simp only [UInt32.reduceOfNat]
  mctrl_norm
  mpay
  -- one piece, no argument
  mstep; mstep
  mstep; mstep [A0]; mstep; mstep [Q4]; mstep; mstep; mstep [Q0]; mstep
  mstep; mstep; mstep [W4]
  mstep; mstep; mstep [W0]
  mstep; mstep; mstep; mstep [P4]
  mcall (f883_spec cfg lim (d + 1) types[32]! (by rfl) inst mi n hn Cg info msg) using [HM]
  · iframe HM
  icases HQ with ⟨%hrs, HM⟩
  subst hrs
  mstep; mstep [P8]
  iapply mwpi_cons
  iapply mwpi_callT' (i := 824) (a := A 824) (type := types[45]!) (inst := inst) (mi := mi)
    (code := f824) [.i32 (sp - 16), .i32 1066380, .i32 msg, .i32 loc]
  isplitr
  · iapply (PanicWithHook.f824_spec cfg lim (d + 1) types[45]! inst mi e A n g ta mx hm (by omega) Cg gt
      (sp - 16) (sp - 16) 1066380 msg loc 181 (A 828) f828 (sp - 16) 1066416 lpc S hS (by omega)
      (by omega) (by decide) iprop(n ↦[i32][ (sp - 16).toNat ] ptr ∗ n ↦[i32][ (sp - 16).toNat + 4 ] len)
      iprop(n ↦[i32][ (sp - 16).toNat ] ptr ∗ n ↦[i32][ (sp - 16).toNat + 4 ] len)
      iprop(n ↦[i32][ info.toNat + 8 ] msg ∗ argsHead n a 1 0 ∗ n ↦[i32][ a.toNat ] pp ∗
        n ↦[i32][ pp.toNat ] ptr ∗ n ↦[i32][ pp.toNat + 4 ] len ∗ D0)
      (6 * cfg.regularOpCost) K bs hpos hlen hutf h hfit hov)
    iframe F828 F473 F474 Hcode Hts
    iapply f828_get cfg lim (d + 2) inst mi Cg n g hn gt (sp - 16 - 32) (sp - 16) (S + 32) (by omega)
  isplitr
  · iexact F824
  isplitr
  · iexact Hi
  isplitr
  · ipureintro; exact ⟨rfl, ha824, rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; simp only [cost824]; mstep_norm_full; omega
  isplitl [Hg Hlo HH Vg Tg HD0 HI HS Hh W0 W4 HM A4 A20 A0 Q0 Q4]
  · iunfold PanicWithHook.pre
    simp only [UInt32.reduceToNat, Nat.reduceAdd]
    iframe Hg HH Vg Tg HI HS Hh
    isplitl [Hlo]
    · iapply stk_addr _ $$ Hlo; omega
    isplitl [W0 W4]
    · iframe W0
      iapply memBytes_congr (by omega) |>.1 $$ W4
    iframe HM A0 Q0 Q4 HD0
    iunfold argsHead
    iframe A4
    iapply memBytes_congr (by simp [UInt32.toNat_add]; omega) |>.1 $$ A20
  inext
  isplit
  · iintro %rs - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexact HT

end Spec

end WNear.Binary.PanicFmt
