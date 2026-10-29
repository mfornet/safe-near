import Bridge.Functions.PanicEntries
import Bridge.Functions.ToStrMsg
import Bridge.Functions.GetFmt

/-!
# `expect_failed` (879) down to the hook's trap, unconditionally

`PanicEntries.f879_full` with its two premises discharged:

* the payload's `get` (826): `GetFmt.f826_expect`, which formats the message into a fresh `String`
  allocated on the heap (once, if the message is not empty) and leaves it in the payload;
* `to_string` on the `PanicInfo` (470): `ToStrMsg.toStr_msg` on `expect_failed`'s
  `format_args!("{}", msg)` (`PanicMsg.msgW_expect`), on the heap 826 leaves (`toStr_expect`, through
  `ToStr_wrap`: the heap's length and live blocks are those `GetSink.gsW` holds).

`f879_unc`: the host panics with `panicText msg file line col`, at `cost879`. What the caller passes:
879's frame (96 bytes) and `S + 80` bytes below 817's stack pointer, `getEnv` (`GetFmt.getData`, the
allocator's vtable slot and the heap) and `hookEnvM` (what the hook's formatting reads besides the
`Arguments`) with any frame `Fr`, the hook installed (`PanicFmt.envP`).

`f853_unc`: `core::panicking::panic` (853), `PanicEntries.f853_full` with `to_string` through
`toStr_str` (`PanicMsg.msgW_str`, one piece); its payload's `get` (828) reads nothing.

The sites: `f879_totalSupplyOverflow` (`internal_deposit`, `core_impl.rs:108:55`, the `Location`
1053040) and `f879_totalSupplyUnderflow` (`internal_withdraw`, `:119:55`, 1053096), on the message
`(1053016, 21)`; the texts are `PanicText.totalSupplyOverflow_text`/`totalSupplyUnderflow_text`.
-/

namespace WNear.Binary.PanicFmtFull

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.FmtWriteN (costN)
open WNear.Binary.FmtWriteT (argsT)
open WNear.Binary.PanicStr (panicSlot panicCode panicked)
open WNear.Binary.PanicHook (ToStr hookCode)
open WNear.Binary.PanicWithHook (hookInstalled infoCells GetSpec)
open WNear.Binary.PanicFmt
open WNear.Binary.PanicEntries (f879_full)
open WNear.Binary.PanicText (panicText)
open WNear.Binary.PanicDisplay (pk12 pptrA plenA pptrB plenB qp qcp XB)
open WNear.Binary.PanicDisplayMsg (XMsg XmT)
open WNear.Binary.PanicMsg (argsH XmX MX0 XS KBX msgW_expect CX)
open WNear.Binary.ToStrMsg (toStr_msg toStrEnvM codeTSM costTSM)
open WNear.Binary.HookSink (HsGlobal costHS)
open WNear.Binary.GetSink (gsW)
open WNear.Binary.GetFmt (getData code826 cost826 f826_expect)
open WNear.Binary.SerdeStruct (MFunSpec_wrap)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `ToStr` on resources that choose an `x` with `φ x`, from `ToStr` on each. -/
theorem ToStr_wrap (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (Cg n g : Nat)
    (gt : GlobalType) (s ip : UInt32) (S : Nat) (K : Nat) (bs : List UInt8) (Hk : IProp GF) [Persistent Hk]
    {α : Type} (φ : α → Prop) (D : IProp GF) (D' : α → IProp GF)
    (hS : ∀ x, φ x → Hk ⊢ ToStr cfg lim d inst mi Cg n g gt s ip S (D' x) K bs)
    (hD : D ⊢ ∃ x, ⌜φ x⌝ ∗ D' x) :
    Hk ⊢ ToStr cfg lim d inst mi Cg n g gt s ip S D K bs := by
  unfold ToStr
  refine MFunSpec_wrap φ
    (P0 := fun x args => iprop(⌜args = [.i32 (s + 16), .i32 ip]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - S) S ∗ stk n (s.toNat + 16) 12 ∗ D' x))
    (Q0 := fun _ _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - S) S ∗
      ∃ ptr cap : UInt32, n ↦[i32][ s.toNat + 16 ] ptr ∗ n ↦[i32][ s.toNat + 20 ] cap ∗
        n ↦[i32][ s.toNat + 24 ] UInt32.ofNat bs.length ∗ n ↦[wms][ ptr.toNat ] bs))
    (fun _ => iprop(emp)) (fun x hx => by have := hS x hx; unfold ToStr at this; exact this) ?_ ?_
  · intro args
    iintro ⟨%ha, Hg, Hs, Ho, HD⟩
    icases hD $$ HD with ⟨%x, %hx, HD⟩
    iexists x
    iframe Hg Hs Ho HD
    isplitr; · ipureintro; exact hx
    ipureintro; exact ha
  · intro x hx args rs
    iintro ⟨-, HQ⟩
    iexact HQ

/-- `gsW`'s heap: its length grown by at most one page, some live blocks. -/
theorem gsW_heap (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (v idx : UInt32) (ta a578 : Nat)
    (w : List UInt8) :
    gsW (GF := GF) n maxP hl live F v idx ta a578 w ⊢ ∃ (hl' : Nat) (live' : List (Nat × Nat)),
      ⌜hl' = hl ∨ hl' = hl + 65536⌝ ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP hl' live' F := by
  iintro H
  iunfold gsW at H
  by_cases hw : w = []
  · simp only [hw, ↓reduceIte]
    icases H with ⟨Hvt, -, -, -, Hinv⟩
    iexists hl, live
    iframe Hvt Hinv
    ipureintro; exact Or.inl rfl
  · simp only [hw, ↓reduceIte]
    icases H with ⟨Hvt, %q, %c, %hl', %tail, %⟨-, -, hhl, -⟩, -, -, -, -, Hinv⟩
    iexists hl', (q.toNat, c.toNat) :: live
    iframe Hvt Hinv
    ipureintro; exact hhl

/-- What the hook's formatting reads on `expect_failed`'s path besides the `Arguments` and the heap:
`XMsg`'s pieces, their arrays and the table entries, the location's, and `to_string`'s sink slot and
piece. -/
def hookEnvM (n ta : Nat) (A : Nat → Nat) (loc file flen line col : UInt32) (fileB : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ 1070672 ] pk12 ∗
    ((n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 ] pptrA 0 ∗
        n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 + 4 ] plenA 0) ∗
      (n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 ] pptrA 1 ∗
        n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 + 4 ] plenA 1) ∗
      ta ↦[wt][ (202 : UInt32).toNat ] Ref.func (A 887)) ∗
    ((n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 ] pptrB 0 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 + 4 ] plenB 0) ∗
      (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 ] pptrB 1 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 + 4 ] plenB 1) ∗
      (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 ] pptrB 2 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 + 4 ] plenB 2) ∗
      ta ↦[wt][ (3 : UInt32).toNat ] Ref.func (A 870)) ∗
    (n ↦[wms][ 1070684 ] qp ∗ n ↦[wms][ 1070685 ] qcp) ∗
    XB n loc file flen line col fileB ∗
    (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759) ∗
      ta ↦[wt][ (104 : UInt32).toNat ] Ref.func (A 469)) ∗
    (n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 ] 1054332 ∗ n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 + 4 ] 0))

/-- The cost of the message's formatting on `to_string`'s sink. -/
noncomputable def costKm (cfg : WasmConfig) (F J B : Nat) : Nat :=
  costN cfg f759 (costHS cfg F J B B) (KBX cfg f759 (costHS cfg F J B B)) 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`to_string` on `expect_failed`'s `PanicInfo`**, after 826: `ToStr` with the bytes
`panicText msg file line col`, on what `f826_expect` leaves and `hookEnvM`. -/
theorem toStr_expect (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 27 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s ip p0 s8 m l loc file flen line col idx : UInt32) (S : Nat) (hS : 432 ≤ S) (hsS : S ≤ s.toNat)
    (hs2 : s.toNat + 28 ≤ 2 ^ 32) (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (hs8 : 1 ≤ s8.toNat) (hs8' : s8.toNat + 56 ≤ 2 ^ 32)
    (msg fileB : List UInt8) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F J : Nat)
    (HG : HsGlobal maxP L0 F J (panicText msg fileB line.toNat col.toNat).length)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl + 65536 ≤ L0) (I Fr : IProp GF) :
    codeTSM n maxP inst mi A ⊢
      ToStr (GF := GF) cfg lim d inst mi Cg n g gt s ip S
        iprop(infoCells n ip (p0 + 4) 1066400 (s8 + 16) loc ∗
          ((n ↦[i32][ p0.toNat ] (s8 + 16) ∗ gsW n maxP hl live F (p0 + 4) idx ta (A 578) msg) ∗
            (argsHead n (s8 + 16) 1 1 ∗ (expectArgs n s8 m l ∗ getData n ta A m msg))) ∗
          (I ∗ (hookEnvM n ta A loc file flen line col fileB ∗ Fr)))
        (costTSM cfg F J (panicText msg fileB line.toNat col.toNat).length
          (costKm cfg F J (panicText msg fileB line.toNat col.toNat).length))
        (panicText msg fileB line.toNat col.toNat) := by
  have ha : (s8 + 16).toNat = s8.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have hx : (s8 + 8).toNat = s8.toNat + 8 := by simp [UInt32.toNat_add]; omega
  have hap : (s8 + 40).toNat = s8.toNat + 40 := by simp [UInt32.toNat_add]; omega
  have ha0 : s8 + 16 ≠ 0 := by
    intro e; have := congrArg UInt32.toNat e; rw [ha] at this; simp at this
  refine ToStr_wrap cfg lim d inst mi Cg n g gt s ip S _ _ _ (α := Nat × List (Nat × Nat))
    (fun x => x.1 = hl ∨ x.1 = hl + 65536) _
    (fun x => iprop(infoCells n ip (p0 + 4) 1066400 (s8 + 16) loc ∗
      (toStrEnvM n ta A maxP x.1 x.2 F idx (s8 + 16) 1070628 (s8 + 40) 1 1 loc file flen line col
        (XmX n ta A 1067136 (s8 + 40) (s8 + 8) m l msg) fileB ∗ iprop(I ∗ Fr)))) ?_ ?_
  · rintro ⟨hl', live'⟩ hx'
    simp only at hx'
    exact toStr_msg cfg lim d inst mi A n g ta hm hd Cg gt s ip (p0 + 4) 1066400 (s8 + 16) 1070628 (s8 + 40) 1 1
      loc file flen line col idx S hS hsS hs2 hip hloc ha0 (by omega)
      (XmX n ta A 1067136 (s8 + 40) (s8 + 8) m l msg)
      (costKm cfg F J (panicText msg fileB line.toNat col.toNat).length) msg fileB hfl hfile hline hcol
      maxP hl' L0 live' F J HG (by rcases hx' with h | h <;> omega) (by rcases hx' with h | h <;> omega)
      (by rcases hx' with h | h <;> omega) iprop(I ∗ Fr)
      (fun dd W => by
        have S := msgW_expect (GF := GF) cfg lim inst mi A n g ta hm (lim.maxCallDepth - 20) (by omega) Cg gt dd
          1065404 157 (s8 + 40) (s8 + 8) m l 1067136 (A 759) f759 W
          (panicText msg fileB line.toNat col.toNat).length
          (costHS cfg F J (panicText msg fileB line.toNat col.toNat).length
            (panicText msg fileB line.toNat col.toNat).length) msg hmsg hml (by rw [hap]; omega)
        rw [show lim.maxCallDepth - 20 + 3 = lim.maxCallDepth - 17 by omega] at S
        refine (?_ : _ ⊢ CX cfg lim (lim.maxCallDepth - 17) inst mi A n g gt dd (A 759) f759 W _ _ Cg).trans S
        iintro ⟨#Hc, #Sw⟩
        iunfold codeTSM at Hc
        icases Hc with ⟨-, #Hk, #H759, -⟩
        iunfold PanicDisplayMsg.code885M at Hk
        icases Hk with ⟨#Hi, -, -, #H856, #H880, -, -, -, -, -⟩
        iunfold CX
        iframe Hi H856 H880 H759 Sw)
  · iintro ⟨HI, ⟨⟨P0, HGs⟩, HA, HE, HD⟩, HI8, HEnv, HFr⟩
    icases gsW_heap n maxP hl live F (p0 + 4) idx ta (A 578) msg $$ HGs with ⟨%hl', %live', %hhl, Hvt, Hinv⟩
    iexists (hl', live')
    isplitr; · ipureintro; exact hhl
    iframe HI HI8 HFr
    iunfold argsHead at HA
    icases HA with ⟨A4, A20⟩
    iunfold expectArgs at HE
    icases HE with ⟨E8, E12, E16, E24, E32, E40, E44, %w28, E28⟩
    iunfold getData at HD
    icases HD with ⟨HPc, T195, Hm, -⟩
    iunfold hookEnvM at HEnv
    icases HEnv with ⟨Hpk, PA, PB, PQ, HXB, HV, HP⟩
    iunfold toStrEnvM, XMsg
    iframe Hpk PA PB PQ HXB HV HP Hvt Hinv
    iunfold argsH, argsT, XmT, XmX, MX0, XS
    rw [ha, hx, hap]
    simp only [UInt32.reduceToNat, Nat.reduceMul, Nat.reduceAdd, Nat.add_zero] at *
    iframe A4 A20 E16 E24 E32 E8 E12 E40 E44 T195 Hm HPc
    iexists w28
    iexact E28


/-! ## `expect_failed` (879) -/

/-- 879's cost on the message `msg` at the location `(file, line, col)`: `PanicEntries.f879_full`'s
with 826 at `cost826` and `to_string` at `costTSM`. -/
noncomputable def cost879 (cfg : WasmConfig) (F J B : Nat) (bs : List UInt8) (h : NearState) : Nat :=
  190 * cfg.regularOpCost + cost817 cfg f826 (cost826 cfg F B) (costTSM cfg F J bs.length
    (costKm cfg F J bs.length)) bs h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`core::option::expect_failed(m, l, loc)`** (879) down to the hook's trap, unconditionally:
with the near-sdk hook installed, the host panicked with `panicText msg file line col`, `msg` the
bytes of `(m, l)` and `(file, flen, line, col)` the `Location` at `loc`. -/
theorem f879_unc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 35 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp m l loc lpc : UInt32) (hloc : loc ≠ 0) (S : Nat) (hS : 432 ≤ S) (hsp : S + 176 ≤ sp.toNat)
    (hsp2 : sp.toNat + 8 ≤ 2 ^ 32) (hal : sp.toNat % 8 = 0)
    (file flen line col idx : UInt32) (hlocb : loc.toNat + 16 ≤ 2 ^ 32)
    (msg fileB : List UInt8) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F J B : Nat)
    (HG : HsGlobal maxP L0 F J (panicText msg fileB line.toNat col.toNat).length)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl + 65536 ≤ L0)
    (hB : 1 ≤ B) (hB2 : B ≤ 65000) (hmB : msg.length ≤ B) (Fr : IProp GF)
    (hlen : (panicText msg fileB line.toNat col.toNat).length < 2 ^ 32)
    (hutf : validUtf8 (panicText msg fileB line.toNat col.toNat) = true) (h : NearState)
    (hfit : LogFits h (panicText msg fileB line.toNat col.toNat).length)
    (hov : h.extCosts.cost "read_memory_byte" * (panicText msg fileB line.toNat col.toNat).length < 2 ^ 64) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
      A 826 ↪[wf] FuncInst.wasm types[14]! inst f826 ∗ code826 n maxP inst mi A ∗ codeTSM n maxP inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f879 Cg
        (fun args => iprop(⌜args = [.i32 m, .i32 l, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗
          (stk n ((sp - 48 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗
            (getData n ta A m msg ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F) ∗
            envP n ta A lpc 1066360 179 (A 826) iprop(hookEnvM n ta A loc file flen line col fileB ∗ Fr) h)))
        (fun _ => cost879 cfg F J B (panicText msg fileB line.toNat col.toNat) h) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h (panicText msg fileB line.toNat col.toNat)) := by
  have hlt := sp.toNat_lt
  have hJ := HG.hJ
  have hF := HG.hF
  have hL1 := HG.hL1
  have hL2 := HG.hL2
  have hpos : 0 < (panicText msg fileB line.toNat col.toNat).length := by
    have : (PanicText.b "panicked at ").length = 12 := by decide +kernel
    simp only [panicText, List.length_append]; omega
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h64 : (sp - 48 - 16).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have h80 : (sp - 48 - 16 - 16).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h64] <;> omega
  have h96 : (sp - 48 - 16 - 16 - 16).toNat = sp.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h80] <;> omega
  have h112 : (sp - 48 - 16 - 16 - 16 - 16).toNat = sp.toNat - 112 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h96] <;> omega
  have h144 : (sp - 48 - 16 - 16 - 16 - 16 - 32).toNat = sp.toNat - 144 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h112] <;> omega
  have h176 : (sp - 48 - 16 - 16 - 16 - 16 - 32 - 32).toNat = sp.toNat - 176 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h144] <;> omega
  have hip : (sp - 48 - 16 - 16 - 16 - 16 - 32 + 16).toNat = sp.toNat - 128 := by
    simp [UInt32.toNat_add, h144]; omega
  iintro ⟨#H859c, #F859, #H817, #F826, #H826, #HTS⟩
  unfold cost879
  iapply (f879_full cfg lim d type inst mi e A n g ta mx hm (by omega) Cg gt sp m l loc lpc hloc S (by omega) hsp
    hal iprop(getData n ta A m msg ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F)
    iprop((n ↦[i32][ (sp - 48 - 16 - 16 - 16 - 16).toNat ] (sp - 48 + 16) ∗
        gsW n maxP hl live F (sp - 48 - 16 - 16 - 16 - 16 + 4) idx ta (A 578) msg) ∗
      (argsHead n (sp - 48 + 16) 1 1 ∗ (expectArgs n (sp - 48) m l ∗ getData n ta A m msg)))
    iprop(hookEnvM n ta A loc file flen line col fileB ∗ Fr) (cost826 cfg F B)
    (costTSM cfg F J (panicText msg fileB line.toNat col.toNat).length
      (costKm cfg F J (panicText msg fileB line.toNat col.toNat).length))
    (panicText msg fileB line.toNat col.toNat) hpos hlen hutf h hfit hov)
  iframe H859c F859 H817 F826
  isplitr
  · iapply (f826_expect cfg lim (d + 6) inst mi A n g ta hm (d + 11) (by omega) (by omega) Cg gt
      (sp - 48 - 16 - 16 - 16 - 16 - 32) (sp - 48 - 16 - 16 - 16 - 16) (sp - 48) m l idx (S + 32) (by omega)
      (by omega) (by omega) (by omega) (by omega) msg hmsg hml maxP hl live F B hF hB hB2 hmB hl0 hl1
      (by omega) (by omega))
    iexact H826
  iapply (toStr_expect cfg lim (d + 8) inst mi A n g ta hm (by omega) Cg gt
    (sp - 48 - 16 - 16 - 16 - 16 - 32 - 32) (sp - 48 - 16 - 16 - 16 - 16 - 32 + 16)
    (sp - 48 - 16 - 16 - 16 - 16) (sp - 48) m l loc file flen line col idx S hS (by omega) (by omega)
    (by omega) hlocb (by omega) (by omega) msg fileB hmsg hml hfl hfile hline hcol maxP hl L0 live F J HG hl0 hl1
    hlL iprop(n ↦[i32][ (sp - 48 - 16).toNat + 8 ] (sp - 48 + 16)) Fr)
  iexact HTS


/-! ## `core::panicking::panic` (853) -/

open WNear.Binary.PanicMsg (XmS msgW_str)
open WNear.Binary.FmtWriteP (costP)
open WNear.Binary.PanicDisplay (SinkW)
open WNear.Binary.PanicEntries (f853_full)

/-- `SinkW` is antitone in its depth bound. -/
theorem SinkW_mono (cfg : WasmConfig) (lim : ExecLimits) (D D' inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) (h : D' ≤ D) :
    SinkW (GF := GF) cfg lim D inst mi n g gt data code W B Kw Cg ⊢
      SinkW cfg lim D' inst mi n g gt data code W B Kw Cg := by
  iintro #Sw
  iunfold SinkW at Sw
  iunfold SinkW
  imodintro
  iintro %d %s %p %k %w %sb %⟨hd, hs, hsb, hp, hwB⟩
  iapply Sw $$ %d %s %p %k %w %sb %⟨by omega, hs, hsb, hp, hwB⟩

/-- The cost of `panic`'s message (one piece) on `to_string`'s sink. -/
noncomputable def costKmS (cfg : WasmConfig) (F J B : Nat) : Nat := costP cfg f759 (costHS cfg F J B B)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`to_string` on `core::panicking::panic`'s `PanicInfo`**: `ToStr` with the bytes
`panicText msg file line col`, on 853's frame, `hookEnvM`, the table entry 195, the message's bytes
and the heap. -/
theorem toStr_str (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 27 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s ip pp0 a0 m l loc file flen line col idx : UInt32) (S : Nat) (hS : 432 ≤ S) (hsS : S ≤ s.toNat)
    (hs2 : s.toNat + 28 ≤ 2 ^ 32) (hip : ip.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (ha0 : 1 ≤ a0.toNat) (ha0b : a0.toNat + 32 ≤ 2 ^ 32)
    (msg fileB : List UInt8) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F J : Nat)
    (HG : HsGlobal maxP L0 F J (panicText msg fileB line.toNat col.toNat).length)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0) (I Fr : IProp GF) :
    codeTSM n maxP inst mi A ⊢
      ToStr (GF := GF) cfg lim d inst mi Cg n g gt s ip S
        iprop(infoCells n ip pp0 1066416 a0 loc ∗ I ∗
          (argsHead n a0 1 0 ∗ n ↦[i32][ a0.toNat ] (a0 + 24) ∗ n ↦[i32][ (a0 + 24).toNat ] m ∗
            n ↦[i32][ (a0 + 24).toNat + 4 ] l ∗
            iprop(n ↦[i32][ a0.toNat + 8 ] 0 ∗ n ↦[i32][ a0.toNat + 16 ] 1067136 ∗
              (∃ w : UInt32, n ↦[i32][ a0.toNat + 12 ] w) ∗
              (hookEnvM n ta A loc file flen line col fileB ∗
                (ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880) ∗ n ↦[wms][ m.toNat ] msg) ∗
                (vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F) ∗ Fr))))
        (costTSM cfg F J (panicText msg fileB line.toNat col.toNat).length
          (costKmS cfg F J (panicText msg fileB line.toNat col.toNat).length))
        (panicText msg fileB line.toNat col.toNat) := by
  have ha24 : (a0 + 24).toNat = a0.toNat + 24 := by simp [UInt32.toNat_add]; omega
  have ha0' : a0 ≠ 0 := by intro e; subst e; simp at ha0
  refine ToStr_wrap cfg lim d inst mi Cg n g gt s ip S _ _ _ (α := Unit) (fun _ => True) _
    (fun _ => iprop(infoCells n ip pp0 1066416 a0 loc ∗
      (toStrEnvM n ta A maxP hl live F idx a0 (a0 + 24) 1067136 1 0 loc file flen line col
        (XmS n (a0 + 24) m l msg) fileB ∗ iprop(I ∗ Fr)))) ?_ ?_
  · intro _ _
    exact toStr_msg cfg lim d inst mi A n g ta hm hd Cg gt s ip pp0 1066416 a0 (a0 + 24) 1067136 1 0
      loc file flen line col idx S hS hsS hs2 hip hloc ha0' (by omega) (XmS n (a0 + 24) m l msg)
      (costKmS cfg F J (panicText msg fileB line.toNat col.toNat).length) msg fileB hfl hfile hline hcol
      maxP hl L0 live F J HG hl0 hl1 hlL iprop(I ∗ Fr)
      (fun dd W => by
        have S := msgW_str (GF := GF) cfg lim inst mi A n g ta hm (lim.maxCallDepth - 20) (by omega) Cg gt dd
          1065404 157 (a0 + 24) m l (A 759) f759 W
          (panicText msg fileB line.toNat col.toNat).length
          (costHS cfg F J (panicText msg fileB line.toNat col.toNat).length
            (panicText msg fileB line.toNat col.toNat).length) msg hmsg hml (by rw [ha24]; omega)
        refine (?_ : _ ⊢ _).trans S
        iintro ⟨#Hc, #Sw⟩
        iunfold codeTSM at Hc
        icases Hc with ⟨-, #Hk, #H759, -⟩
        iunfold PanicDisplayMsg.code885M at Hk
        icases Hk with ⟨#Hi, -⟩
        iframe Hi H759
        iapply SinkW_mono cfg lim (lim.maxCallDepth - 17) _ inst mi n g gt dd f759 W _ _ Cg (by omega) $$ Sw)
  · iintro ⟨HI, HI8, HA, P0, P24, P28, P8, P16, ⟨%w12, P12⟩, HEnv, ⟨T195, Hm⟩, ⟨Hvt, Hinv⟩, HFr⟩
    iexists ()
    isplitr; · ipureintro; trivial
    iframe HI HI8 HFr
    iunfold argsHead at HA
    icases HA with ⟨A4, A20⟩
    iunfold hookEnvM at HEnv
    icases HEnv with ⟨Hpk, PA, PB, PQ, HXB, HV, HP⟩
    iunfold toStrEnvM, XMsg
    iframe Hpk PA PB PQ HXB HV HP Hvt Hinv
    iunfold argsH, argsT, XmT, XmS
    iframe A4 A20 P0 P8 P16 P24 P28 T195 Hm
    iexists w12
    iexact P12

/-- 853's cost on the message `msg` at the location `(file, line, col)`. -/
noncomputable def cost853 (cfg : WasmConfig) (F J : Nat) (bs : List UInt8) (h : NearState) : Nat :=
  180 * cfg.regularOpCost + cost817 cfg f828 (6 * cfg.regularOpCost)
    (costTSM cfg F J bs.length (costKmS cfg F J bs.length)) bs h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`core::panicking::panic(m, l, loc)`** (853) down to the hook's trap, unconditionally: with
the near-sdk hook installed, the host panicked with `panicText msg file line col`. -/
theorem f853_unc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 35 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp m l loc lpc : UInt32) (hloc : loc ≠ 0) (S : Nat) (hS : 432 ≤ S) (hsp : S + 160 ≤ sp.toNat)
    (hsp2 : sp.toNat + 8 ≤ 2 ^ 32) (hal : sp.toNat % 8 = 0)
    (file flen line col idx : UInt32) (hlocb : loc.toNat + 16 ≤ 2 ^ 32)
    (msg fileB : List UInt8) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F J : Nat)
    (HG : HsGlobal maxP L0 F J (panicText msg fileB line.toNat col.toNat).length)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl ≤ L0) (Fr : IProp GF)
    (hlen : (panicText msg fileB line.toNat col.toNat).length < 2 ^ 32)
    (hutf : validUtf8 (panicText msg fileB line.toNat col.toNat) = true) (h : NearState)
    (hfit : LogFits h (panicText msg fileB line.toNat col.toNat).length)
    (hov : h.extCosts.cost "read_memory_byte" * (panicText msg fileB line.toNat col.toNat).length < 2 ^ 64) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
      A 828 ↪[wf] FuncInst.wasm types[14]! inst f828 ∗ codeTSM n maxP inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f853 Cg
        (fun args => iprop(⌜args = [.i32 m, .i32 l, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗
          (stk n ((sp - 32 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗
            envP n ta A lpc 1066380 181 (A 828) iprop(hookEnvM n ta A loc file flen line col fileB ∗
              (ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880) ∗ n ↦[wms][ m.toNat ] msg) ∗
              (vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F) ∗ Fr) h)))
        (fun _ => cost853 cfg F J (panicText msg fileB line.toNat col.toNat) h) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h (panicText msg fileB line.toNat col.toNat)) := by
  have hlt := sp.toNat_lt
  have hpos : 0 < (panicText msg fileB line.toNat col.toNat).length := by
    have : (PanicText.b "panicked at ").length = 12 := by decide +kernel
    simp only [panicText, List.length_append]; omega
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h48 : (sp - 32 - 16).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h32] <;> omega
  have h64 : (sp - 32 - 16 - 16).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have h80 : (sp - 32 - 16 - 16 - 16).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h64] <;> omega
  have h96 : (sp - 32 - 16 - 16 - 16 - 16).toNat = sp.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h80] <;> omega
  have h128 : (sp - 32 - 16 - 16 - 16 - 16 - 32).toNat = sp.toNat - 128 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h96] <;> omega
  have h160 : (sp - 32 - 16 - 16 - 16 - 16 - 32 - 32).toNat = sp.toNat - 160 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h128] <;> omega
  have hip : (sp - 32 - 16 - 16 - 16 - 16 - 32 + 16).toNat = sp.toNat - 112 := by
    simp [UInt32.toNat_add, h128]; omega
  iintro ⟨#H859c, #F859, #H817, #F828, #HTS⟩
  unfold cost853
  iapply (f853_full cfg lim d type inst mi e A n g ta mx hm (by omega) Cg gt sp m l loc lpc hloc S (by omega) hsp
    hal iprop(hookEnvM n ta A loc file flen line col fileB ∗
      (ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880) ∗ n ↦[wms][ m.toNat ] msg) ∗
      (vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F) ∗ Fr)
    (costTSM cfg F J (panicText msg fileB line.toNat col.toNat).length
      (costKmS cfg F J (panicText msg fileB line.toNat col.toNat).length))
    (panicText msg fileB line.toNat col.toNat) hpos hlen hutf h hfit hov)
  iframe H859c F859 H817 F828
  have T := toStr_str cfg lim (d + 8) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32 - 16 - 16 - 16 - 16 - 32 - 32) (sp - 32 - 16 - 16 - 16 - 16 - 32 + 16)
    (sp - 32 - 16 - 16 - 16 - 16) (sp - 32) m l loc file flen line col idx S hS (by omega) (by omega)
    (by omega) hlocb (by omega) (by omega) msg fileB hmsg hml hfl hfile hline hcol maxP hl L0 live F J HG hl0 hl1
    hlL iprop((n ↦[i32][ (sp - 32 - 16 - 16 - 16 - 16).toNat ] m ∗
      n ↦[i32][ (sp - 32 - 16 - 16 - 16 - 16).toNat + 4 ] l) ∗ n ↦[i32][ (sp - 32 - 16).toNat + 8 ] (sp - 32)) Fr
  iapply (ToStr_wrap cfg lim (d + 8) inst mi Cg n g gt (sp - 32 - 16 - 16 - 16 - 16 - 32 - 32)
    (sp - 32 - 16 - 16 - 16 - 16 - 32 + 16) S _ _ (codeTSM n maxP inst mi A) (α := Unit) (fun _ => True) _ (fun _ => _)
    (fun _ _ => T) ?_)
  · iintro ⟨HI, HP, I8, HA, P0, P24, P28, P8, P16, P12, HD1⟩
    iexists ()
    isplitr; · ipureintro; trivial
    iframe HI HA P0 P24 P28 P8 P16 P12 HD1 HP I8
  · iexact HTS


/-! ## `internal_deposit`'s and `internal_withdraw`'s `expect("Total supply overflow")` -/

open WNear.Binary.PanicText (totalSupplyOverflow coreImplRs totalSupplyOverflow_valid decDigits_108
  decDigits_119 decDigits_55)

theorem totalSupplyOverflow_text_length :
    (panicText totalSupplyOverflow coreImplRs (108 : UInt32).toNat (55 : UInt32).toNat).length = 163 := by
  rw [show (108 : UInt32).toNat = 108 from rfl, show (55 : UInt32).toNat = 55 from rfl, panicText, decDigits_108,
    decDigits_55]
  decide +kernel

theorem totalSupplyUnderflow_text_length :
    (panicText totalSupplyOverflow coreImplRs (119 : UInt32).toNat (55 : UInt32).toNat).length = 163 := by
  rw [show (119 : UInt32).toNat = 119 from rfl, show (55 : UInt32).toNat = 55 from rfl, panicText, decDigits_119,
    decDigits_55]
  decide +kernel

theorem totalSupplyUnderflow_valid :
    validUtf8 (panicText totalSupplyOverflow coreImplRs 119 55) = true := by
  rw [panicText, decDigits_119, decDigits_55]; decide +kernel

/-- The sink's bounds for a text of at most 256 bytes: at most six growths. -/
theorem hsGlobal_256 {maxP L0 F B : Nat} (hF : 1 ≤ F) (hB : B ≤ 256) (hL1 : L0 + 7 * 65536 ≤ 2 ^ 32)
    (hL2 : L0 + 6 * 65536 ≤ maxP * 65536) : HsGlobal maxP L0 F 6 B :=
  ⟨hF, by decide, by simp; omega, by omega, hL1, hL2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`expect("Total supply overflow")`** in `internal_deposit` (`near_deposit`, `core_impl.rs:108:55`):
879 on `(1053016, 21)` at the `Location` 1053040; the host panicked with the text
`PanicText.totalSupplyOverflow_text` identifies as `Panic.message .totalSupplyOverflow`. -/
theorem f879_totalSupplyOverflow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 35 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp lpc idx : UInt32) (S : Nat) (hS : 432 ≤ S) (hsp : S + 176 ≤ sp.toNat)
    (hsp2 : sp.toNat + 8 ≤ 2 ^ 32) (hal : sp.toNat % 8 = 0)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : 1 ≤ F) (hL1 : L0 + 7 * 65536 ≤ 2 ^ 32)
    (hL2 : L0 + 6 * 65536 ≤ maxP * 65536) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl + 65536 ≤ L0)
    (Fr : IProp GF) (h : NearState) (hfit : LogFits h 163)
    (hov : h.extCosts.cost "read_memory_byte" * 163 < 2 ^ 64) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
      A 826 ↪[wf] FuncInst.wasm types[14]! inst f826 ∗ code826 n maxP inst mi A ∗ codeTSM n maxP inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f879 Cg
        (fun args => iprop(⌜args = [.i32 1053016, .i32 21, .i32 1053040]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗
          (stk n ((sp - 48 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗
            (getData n ta A 1053016 totalSupplyOverflow ∗ vt n 1057464 idx ta (A 578) ∗
              heapInv n maxP hl live F) ∗
            envP n ta A lpc 1066360 179 (A 826)
              iprop(hookEnvM n ta A 1053040 1052816 119 108 55 coreImplRs ∗ Fr) h)))
        (fun _ => cost879 cfg F 6 21 (panicText totalSupplyOverflow coreImplRs 108 55) h)
        (fun _ _ => iprop(False)) (fun _ => panicked Cg h (panicText totalSupplyOverflow coreImplRs 108 55)) := by
  have hT := totalSupplyOverflow_text_length
  have S := f879_unc (GF := GF) cfg lim d type inst mi e A n g ta mx hm hd Cg gt sp 1053016 21 1053040 lpc
    (by decide) S hS hsp hsp2 hal 1052816 119 108 55 idx (by decide) totalSupplyOverflow coreImplRs
    (by decide +kernel) (by decide) (by decide +kernel) (by decide) (by decide) (by decide) maxP hl L0 live F 6 21
    (hsGlobal_256 hF (by rw [hT]; decide) hL1 hL2) hl0 hl1 hlL (by decide) (by decide) (by decide +kernel) Fr
    (by rw [hT]; decide) totalSupplyOverflow_valid h (by rw [hT]; exact hfit) (by rw [hT]; exact hov)
  exact S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`expect("Total supply overflow")`** in `internal_withdraw` (`near_withdraw`, `core_impl.rs:119:55`):
879 on `(1053016, 21)` at the `Location` 1053096; the text is `Panic.message .totalSupplyUnderflow`
(`PanicText.totalSupplyUnderflow_text`). -/
theorem f879_totalSupplyUnderflow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 35 ≤ lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp lpc idx : UInt32) (S : Nat) (hS : 432 ≤ S) (hsp : S + 176 ≤ sp.toNat)
    (hsp2 : sp.toNat + 8 ≤ 2 ^ 32) (hal : sp.toNat % 8 = 0)
    (maxP hl L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : 1 ≤ F) (hL1 : L0 + 7 * 65536 ≤ 2 ^ 32)
    (hL2 : L0 + 6 * 65536 ≤ maxP * 65536) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hlL : hl + 65536 ≤ L0)
    (Fr : IProp GF) (h : NearState) (hfit : LogFits h 163)
    (hov : h.extCosts.cost "read_memory_byte" * 163 < 2 ^ 64) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
      A 826 ↪[wf] FuncInst.wasm types[14]! inst f826 ∗ code826 n maxP inst mi A ∗ codeTSM n maxP inst mi A
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f879 Cg
        (fun args => iprop(⌜args = [.i32 1053016, .i32 21, .i32 1053096]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗
          (stk n ((sp - 48 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗
            (getData n ta A 1053016 totalSupplyOverflow ∗ vt n 1057464 idx ta (A 578) ∗
              heapInv n maxP hl live F) ∗
            envP n ta A lpc 1066360 179 (A 826)
              iprop(hookEnvM n ta A 1053096 1052816 119 119 55 coreImplRs ∗ Fr) h)))
        (fun _ => cost879 cfg F 6 21 (panicText totalSupplyOverflow coreImplRs 119 55) h)
        (fun _ _ => iprop(False)) (fun _ => panicked Cg h (panicText totalSupplyOverflow coreImplRs 119 55)) := by
  have hT := totalSupplyUnderflow_text_length
  have S := f879_unc (GF := GF) cfg lim d type inst mi e A n g ta mx hm hd Cg gt sp 1053016 21 1053096 lpc
    (by decide) S hS hsp hsp2 hal 1052816 119 119 55 idx (by decide) totalSupplyOverflow coreImplRs
    (by decide +kernel) (by decide) (by decide +kernel) (by decide) (by decide) (by decide) maxP hl L0 live F 6 21
    (hsGlobal_256 hF (by rw [hT]; decide) hL1 hL2) hl0 hl1 hlL (by decide) (by decide) (by decide +kernel) Fr
    (by rw [hT]; decide) totalSupplyUnderflow_valid h (by rw [hT]; exact hfit) (by rw [hT]; exact hov)
  exact S

end Spec

end WNear.Binary.PanicFmtFull
