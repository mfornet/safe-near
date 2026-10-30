import Bridge.Functions.PanicHook
import Bridge.Functions.SetupPanicHook
import Bridge.Functions.FmtWrite

/-!
# `std::panicking::rust_panic_with_hook` (824), up to the hook's trap

Rust 1.51's `rust_panic_with_hook(payload: &mut dyn BoxMeUp, message: Option<&Arguments>,
location: &Location) -> !`, as the binary has it:

```wat
;; 824 (p0, vt, msg, loc)                    ;; the payload (p0, vt)
sp -= 32;  l5 := 1
[1074932] += 1                               ;; GLOBAL_PANIC_COUNT
if [1074936] ≠ 1:  [1074936] := (1, 1)       ;; LOCAL_PANIC_COUNT: (initialised, 1)
else: l5 := ++[1074940];  l5 ≥ 3 ⇒ abort    ;; (unreachable: a trap, no message)
[sp+28] := loc;  [sp+24] := msg;  [sp+16], [sp+20] := 1065704, 1065704   ;; the PanicInfo
l2 := [1074920];  l2 <s 0 ⇒ abort            ;; HOOK_LOCK, taken for writing
[1074920] := l2 + 1                          ;; read lock
if [1074928] ≠ 0:                            ;; Hook::Custom (data [1074924], vtable [1074928])
  call_indirect[[vt + 16]](sp + 8, p0)       ;; payload.get(): the &dyn Any (ptr, vtable) at sp + 8
  [sp+16..24] := [sp+8..16]                   ;; info.payload
  call_indirect[[[1074928] + 12]]([1074924], sp + 16)   ;; hook(&info)
[1074920] -= 1;  l5 ≥ 2 ⇒ abort;  rust_panic(p0, vt) (831)   ;; not reached: the hook traps
```

There is no default hook in this binary: with `[1074928] = 0` the hook is skipped and the panic
goes on to `rust_panic` (831, `__rust_start_panic`, an abort), with no message. A double panic
(`[1074936] = 1` and the count reaching 3) aborts before the hook, also with no message.

`SetupPanicHook` leaves the hook `(1, 1055136)` with the lock free and the global count zero
(`hookCells n 0 1 1055136`); a fresh instance has `LOCAL_PANIC_COUNT` zero. The hook's vtable word at
`1055136 + 12` is the table index 118 (`vtable_hook`), whose entry is 473 (`wTable_hook`).

`f824_spec` is parametric in the payload's `get` (its code `codeG` at the table entry `[vt + 16]`, any
`MFunSpec` writing the `&dyn Any` `(pp, pv)` at `sp - 32 + 8`, `GetSpec`) and in `to_string`'s
specification (`PanicHook.ToStr`) on the `PanicInfo` at `sp - 32 + 16`: `(pp, pv, msg, loc)`
(`infoCells`), with the resources `G'` the payload's `get` leaves and any others `D0`. It traps,
the host panicked with the bytes `to_string` writes.

Cost: `cost824`, `92` `regular_op_cost`s, `get`'s activation and cost, and the hook (473's 11 and
`cost474`).
-/

namespace WNear.Binary.PanicWithHook

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface
open WNear.Binary.PanicStr (panicSlot panicCode panicked mwpi_callT' mwpi_call_indirectT')
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr)
open WNear.Binary.PanicHook (ToStr hookCode hookPre cost474 stk4_word stk_split')
open WNear.Binary.SetupPanicHook (hookCells)

/-! ## The data -/

/-- The hook's vtable (1055136): `call` at the table index 118. -/
theorem vtable_hook : dataWord (1055136 + 12) = bytes32 118 := by
  rw [dataWord_eq _ (by decide)]; decide

set_option maxRecDepth 100000 in
/-- The table entry 118: 473. -/
theorem wTable_hook : wTable.elems[118]? = some (Ref.func 473) := rfl

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **The hook installed**: the static cells as `setup_panic_hook` leaves them, the thread's panic
count not initialised, and the hook's vtable slot (the table index 118, its entry 473). -/
def hookInstalled (n ta : Nat) (A : Nat → Nat) (lpc : UInt32) : IProp GF :=
  iprop(hookCells n 0 1 1055136 ∗ n ↦[i32][ 1074936 ] 0 ∗ n ↦[i32][ 1074940 ] lpc ∗
    n ↦[i32][ 1055136 + 12 ] 118 ∗ ta ↦[wt][ 118 ] Ref.func (A 473))

/-- The `PanicInfo` at `ip`: the payload `(pp, pv)`, the message and the location. -/
def infoCells (n : Nat) (ip pp pv msg loc : UInt32) : IProp GF :=
  iprop(n ↦[i32][ ip.toNat ] pp ∗ n ↦[i32][ ip.toNat + 4 ] pv ∗ n ↦[i32][ ip.toNat + 8 ] msg ∗
    n ↦[i32][ ip.toNat + 12 ] loc)

/-- **What the payload's `get` is asked**: called with the stack pointer `s` on the payload `p0`,
within `S` bytes of stack below `s`, it writes the `&dyn Any` `(pp, pv)` at `s + 8`. -/
def GetSpec (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (s p0 pp pv : UInt32) (S : Nat) (code : Func) (G G' : IProp GF) (K : Nat) :
    IProp GF :=
  MFunSpec cfg lim d types[14]! inst mi code Cg
    (fun args => iprop(⌜args = [.i32 (s + 8), .i32 p0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - S) S ∗ stk n (s.toNat + 8) 8 ∗ G))
    (fun _ => K)
    (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - S) S ∗
      n ↦[i32][ s.toNat + 8 ] pp ∗ n ↦[i32][ s.toNat + 12 ] pv ∗ G'))

instance (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (s p0 pp pv : UInt32) (S : Nat) (code : Func) (G G' : IProp GF) (K : Nat) :
    Persistent (GetSpec cfg lim d inst mi Cg n g gt s p0 pp pv S code G G' K) := by
  unfold GetSpec; infer_instance

/-- 824's precondition: the payload `(p0, vt)`, the message and the location; the stack pointer
and `S + 64` bytes below it; the hook installed; the payload vtable's `get` slot; `get`'s
resources `G`, the others `D0`; the interface, the `panic_utf8` slot and the host. -/
def pre (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (sp p0 vt msg loc gidx : UInt32) (ag : Nat)
    (lpc : UInt32) (S : Nat) (G D0 : IProp GF) (h : NearState) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 p0, .i32 vt, .i32 msg, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
    stk n (sp.toNat - 64 - S) (S + 64) ∗ hookInstalled n ta A lpc ∗
    n ↦[i32][ vt.toNat + 16 ] gidx ∗ ta ↦[wt][ gidx.toNat ] Ref.func ag ∗ G ∗ D0 ∗
    iface n ta A ∗ panicSlot n ta A ∗ mhostPt h)

/-- 824's cost: `get`'s and the hook's. -/
def cost824 (cfg : WasmConfig) (codeG : Func) (Kg K : Nat) (bs : List UInt8) (h : NearState) : Nat :=
  92 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals codeG [.i32 0, .i32 0]) + Kg +
    cost474 cfg K bs h

theorem stk824 (n : Nat) (sp : UInt32) (S : Nat) (hsp : S + 64 ≤ sp.toNat) :
    stk (GF := GF) n (sp.toNat - 64 - S) (S + 64) ⊢
      stk n ((sp - 32).toNat - (S + 32)) (S + 32) ∗ stk n (sp - 32).toNat 8 ∗
        stk n ((sp - 32).toNat + 8) 8 ∗ stk n ((sp - 32).toNat + 16) 16 := by
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iintro H
  icases stk_split n _ (S + 32) 32 $$ H with ⟨H1, H⟩
  icases stk_split n _ 8 24 $$ H with ⟨H2, H⟩
  icases stk_split n _ 8 16 $$ H with ⟨H3, H4⟩
  rw [h32]
  isplitl [H1]
  · iapply stk_addr _ $$ H1; omega
  isplitl [H2]
  · iapply stk_addr _ $$ H2; omega
  isplitl [H3]
  · iapply stk_addr _ $$ H3; omega
  iapply stk_addr _ $$ H4; omega

theorem i64_11 : storeBytes (.i64 4294967297) 8 = bytes32 1 ++ bytes32 1 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`rust_panic_with_hook(payload, message, location)`** (824) with the near-sdk hook installed
and no panic in progress: the payload's `get` (`GetSpec`), then the hook (473) on the `PanicInfo`
`(pp, pv, msg, loc)` (`infoCells`), whose `to_string` (`ToStr`) writes `bs`: a trap, the host
panicked with `bs`. -/
theorem f824_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp p0 vt msg loc gidx : UInt32) (ag : Nat) (codeG : Func) (pp pv lpc : UInt32) (S : Nat)
    (hS : 32 ≤ S) (hsp : S + 64 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hvt : vt.toNat + 20 ≤ 2 ^ 32)
    (G G' D0 : IProp GF) (Kg K : Nat) (bs : List UInt8) (hpos : 0 < bs.length)
    (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hfit : LogFits h bs.length) (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    ag ↪[wf] FuncInst.wasm types[14]! inst codeG ∗
      GetSpec cfg lim (d + 1) inst mi Cg n g gt (sp - 32) p0 pp pv (S + 32) codeG G G' Kg ∗
      A 473 ↪[wf] FuncInst.wasm types[14]! inst f473 ∗ A 474 ↪[wf] FuncInst.wasm types[0]! inst f474 ∗
      hookCode e inst mi A n mx ∗
      ToStr cfg lim (d + 3) inst mi Cg n g gt (sp - 32 - 32) (sp - 32 + 16) S
        iprop(infoCells n (sp - 32 + 16) pp pv msg loc ∗ G' ∗ D0) K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f824 Cg
        (pre n g ta A gt sp p0 vt msg loc gidx ag lpc S G D0 h)
        (fun _ => cost824 cfg codeG Kg K bs h) (fun _ _ => iprop(False)) (fun _ => panicked Cg h bs) := by
  iintro ⟨#FG, #Sg, #F473, #F474, #Hcode, #Hts⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold hookCode, panicCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have hta := hm.table
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (sp - 32 + 8).toNat = (sp - 32).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have e16 : (sp - 32 + 16).toNat = (sp - 32).toNat + 16 := by simp [UInt32.toNat_add]; omega
  iapply MFunSpecT_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hg, Hs, HH, Vg, Tg, HG, HD0, HI, HS, Hh⟩
  subst hargs
  iunfold hookInstalled, hookCells at HH
  icases HH with ⟨⟨Gpc, Lk, Hd, Hv⟩, L0, L1, V12, T118⟩
  icases stk824 n sp S hsp $$ Hs with ⟨Hlo, -, H8, Hinfo⟩
  ihave Gpc := (memBytes_congr (j := (0 : UInt32).toNat + 1074932) (by simp)).1 $$ Gpc
  ihave Lk := (memBytes_congr (j := (0 : UInt32).toNat + 1074920) (by simp)).1 $$ Lk
  ihave Hd := (memBytes_congr (j := (0 : UInt32).toNat + 1074924) (by simp)).1 $$ Hd
  ihave Hv := (memBytes_congr (j := (0 : UInt32).toNat + 1074928) (by simp)).1 $$ Hv
  ihave L0 := (memBytes_congr (j := (0 : UInt32).toNat + 1074936) (by simp)).1 $$ L0
  simp only [f824, cost824]
  generalize hAG : activationGas cfg.regularOpCost (entryLocals codeG [.i32 0, .i32 0]) = AG
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  -- GLOBAL_PANIC_COUNT += 1
  mstep; mstep; mstep [Gpc]; mstep; mstep; mstep [Gpc]
  -- LOCAL_PANIC_COUNT: (1, 1)
  mstep; mstep; mstep
  mstep; mstep [L0]; mstep; mstep; mstep
  ihave L01 := (memBytes_append n 1074936 (bytes32 0) (bytes32 lpc)).2 $$ [L0 L1]
  · isplitl [L0]
    · iexact L0
    iapply memBytes_congr (by simp) |>.1 $$ L1
  mstep; mstep; mstep [L01]
  mstep
  -- the PanicInfo
  icases VecFromElem.stk16 n _ $$ Hinfo with ⟨I16, I20, I24, I28⟩
  icases stk4_word n _ $$ I16 with ⟨%i16, I16⟩
  icases stk4_word n _ $$ I20 with ⟨%i20, I20⟩
  icases stk4_word n _ $$ I24 with ⟨%i24, I24⟩
  icases stk4_word n _ $$ I28 with ⟨%i28, I28⟩
  ihave I20 := memBytes_congr (j := (sp - 32).toNat + 20) (by omega) |>.1 $$ I20
  ihave I24 := memBytes_congr (j := (sp - 32).toNat + 24) (by omega) |>.1 $$ I24
  ihave I28 := memBytes_congr (j := (sp - 32).toNat + 28) (by omega) |>.1 $$ I28
  mstep; mstep; mstep [I28]
  mstep; mstep; mstep [I24]
  mstep; mstep; mstep [I20]
  mstep; mstep; mstep [I16]
  -- HOOK_LOCK: free, read-locked
  mstep; mstep [Lk]; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep [Lk]
  -- Hook::Custom
  mstep
  mstep; mstep [Hv]; mstep; mstep; mstep
  mstep; mstep [Hd]; mstep
  -- payload.get()
  icases stk_split n _ 4 4 $$ H8 with ⟨H8, H12⟩
  mstep; mstep; mstep; mstep; mstep; mstep [Vg]
  iapply mwpi_cons
  iapply (Borrow.mwpi_call_indirect' (ty := 14) (t := 0) (ta := ta) (idx := gidx) (a := ag)
    (type := types[14]!) (inst := inst) (mi := mi) (code := codeG) [.i32 (sp - 32 + 8), .i32 p0])
  isplitr
  · iunfold GetSpec at Sg; iexact Sg
  isplitr
  · iexact FG
  isplitr
  · iexact Hi
  isplitl [Tg]
  · iexact Tg
  isplitr
  · ipureintro; exact ⟨rfl, hta, by simp [hm.types], rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; rw [FmtWrite.act2, hAG]; omega
  isplitl [Hg Hlo H8 H12 HG]
  · iframe Hg Hlo HG
    isplitr
    · ipureintro; rfl
    iapply stk_join n _ 4 4
    iframe H8
    iapply stk_addr _ $$ H12; omega
  inext
  iintro %rs Tg Hc HQ
  icases HQ with ⟨%hrs, Hg, Hlo, P8, P12, HG'⟩
  subst hrs
  rw [FmtWrite.act2, hAG]
  mcredits (31 * cfg.regularOpCost + cost474 cfg K bs h + R)
  mstep_post
  -- info.payload := the &dyn Any
  ihave P := (memBytes_append n ((sp - 32).toNat + 8) (bytes32 pp) (bytes32 pv)).2 $$ [P8 P12]
  · isplitl [P8]
    · iexact P8
    iapply memBytes_congr (by simp) |>.1 $$ P12
  ihave I := (memBytes_append n ((sp - 32).toNat + 16) (bytes32 1065704) (bytes32 1065704)).2 $$ [I16 I20]
  · isplitl [I16]
    · iexact I16
    iapply memBytes_congr (by simp) |>.1 $$ I20
  mstep; mstep; mstep [P]; mstep [I]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  icases (memBytes_append n ((sp - 32).toNat + 16) (bytes32 pp) (bytes32 pv)).1 $$ I with ⟨I16, I20⟩
  mstep; mstep; mstep; mstep; mstep
  simp only [UInt32.reduceOfNat]
  mstep [V12]
  -- the hook: 473, then 474, which traps
  iapply mwpi_cons
  iapply (mwpi_call_indirectT' (ty := 14) (t := 0) (ta := ta) (idx := 118) (a := A 473)
    (type := types[14]!) (inst := inst) (mi := mi) (code := f473)
    [.i32 (UInt32.ofNat 1), .i32 (sp - 32 + 16)])
  isplitr
  · iapply (PanicHook.f473_spec cfg lim (d + 1) types[14]! inst mi e A n g ta mx hm (by omega) Cg gt
      (sp - 32) (UInt32.ofNat 1) (sp - 32 + 16) S hS (by omega) (by omega)
      iprop(infoCells n (sp - 32 + 16) pp pv msg loc ∗ G' ∗ D0) K bs hpos hlen hutf h hfit hov)
    iframe F474 Hcode Hts
  isplitr
  · iexact F473
  isplitr
  · iexact Hi
  isplitl [T118]
  · simp only [UInt32.reduceToNat]; iexact T118
  isplitr
  · ipureintro; exact ⟨rfl, hta, by simp [hm.types], rfl, by omega⟩
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hg Hlo HI HS Hh I16 I20 I24 I28 HG' HD0]
  · isplitr
    · ipureintro; rfl
    iunfold hookPre
    iframe Hg HI HS Hh HG' HD0
    isplitr
    · ipureintro; rfl
    isplitl [Hlo]
    · iapply stk_addr _ $$ Hlo; omega
    iunfold infoCells
    rw [e16]
    iframe I16
    isplitl [I20]
    · iapply memBytes_congr (by simp) |>.1 $$ I20
    isplitl [I24]
    · iapply memBytes_congr (by omega) |>.1 $$ I24
    iapply memBytes_congr (by omega) |>.1 $$ I28
  inext
  isplit
  · iintro %rs - - HF
    iexfalso
    iexact HF
  · iintro HT
    simp only [Post.mseq_trap, Post.mblock, Post.mfunc]
    iexact HT

end Spec

end WNear.Binary.PanicWithHook
