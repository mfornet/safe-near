import Bridge.Functions.PanicFmt

/-!
# The panic entries, composed down to the hook's trap

`expect_failed` (879) and `core::panicking::panic` (853) with 859, 823, 816 and the right branch of
817 (`PanicFmt.f817_fmt`, `PanicFmt.f817_str`) plugged in. What is left as premises:

* `to_string` on the `PanicInfo` (`PanicHook.ToStr`), which fixes the bytes `bs` the host
  panics with: `<PanicInfo as Display>` (885) with the message `Some(args)`;
* for 879, the payload's `get` (826, `GetSpec`), which formats the message into a fresh `String`
  (the binary does it although the hook does not read it).

`begin_panic` (664) needs no composition: `PanicBegin.f664_spec`.

The stack: the entry's frames (`stk n (sp.toNat - 96) 96` for 879, 80 for 853) and, below them,
817's `S + 80` bytes, `stk n (s817.toNat - 80 - S) (S + 80)`, `s817` the stack pointer 817 runs at.
-/

namespace WNear.Binary.PanicEntries

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface
open WNear.Binary.PanicStr (panicSlot panicCode panicked)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.PanicHook (ToStr hookCode)
open WNear.Binary.PanicWithHook (hookInstalled infoCells GetSpec)
open WNear.Binary.PanicFmt

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- **`core::option::expect_failed(m, l, loc)`** (879) down to the hook's trap: with the near-sdk
hook installed, the host panicked with the bytes `to_string` writes on the `PanicInfo`
`(payload, message Some(format_args!("{}", (m, l))), location loc)`. -/
theorem f879_full (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp m l loc lpc : UInt32) (hloc : loc ≠ 0) (S : Nat) (hS : 32 ≤ S) (hsp : S + 176 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (Ga G' D1 : IProp GF) (Kg K : Nat) (bs : List UInt8)
    (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hfit : LogFits h bs.length) (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
      A 826 ↪[wf] FuncInst.wasm types[14]! inst f826 ∗
      GetSpec cfg lim (d + 6) inst mi Cg n g gt (sp - 48 - 16 - 16 - 16 - 16 - 32) (sp - 48 - 16 - 16 - 16 - 16)
        (sp - 48 - 16 - 16 - 16 - 16 + 4) 1066400 (S + 32) f826
        iprop(fmtPayload n (sp - 48 - 16 - 16 - 16 - 16) (sp - 48 + 16) ∗ Ga) G' Kg ∗
      ToStr cfg lim (d + 8) inst mi Cg n g gt (sp - 48 - 16 - 16 - 16 - 16 - 32 - 32)
        (sp - 48 - 16 - 16 - 16 - 16 - 32 + 16) S
        iprop(infoCells n (sp - 48 - 16 - 16 - 16 - 16 - 32 + 16) (sp - 48 - 16 - 16 - 16 - 16 + 4) 1066400
            (sp - 48 + 16) loc ∗ G' ∗
          (n ↦[i32][ (sp - 48 - 16).toNat + 8 ] (sp - 48 + 16) ∗ argsHead n (sp - 48 + 16) 1 1 ∗
            iprop(expectArgs n (sp - 48) m l ∗ D1))) K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f879 Cg
        (fun args => iprop(⌜args = [.i32 m, .i32 l, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 96) 96 ∗
          (stk n ((sp - 48 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗ Ga ∗
            envP n ta A lpc 1066360 179 (A 826) D1 h)))
        (fun _ => 190 * cfg.regularOpCost + cost817 cfg f826 Kg K bs h) (fun _ _ => iprop(False))
        (fun _ => panicked Cg h bs) := by
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h64 : (sp - 48 - 16).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have h80 : (sp - 48 - 16 - 16).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h64] <;> omega
  have h96 : (sp - 48 - 16 - 16 - 16).toNat = sp.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h80] <;> omega
  have e16 : (sp - 48 + 16).toNat = (sp - 48).toNat + 16 := by simp [UInt32.toNat_add]; omega
  iintro ⟨#H859, #F859, #H817, #F826, #Sg, #Hts⟩
  ihave #S817 := f817_fmt cfg lim (d + 4) inst mi e A n g ta mx hm (by omega) Cg gt
    (sp - 48 - 16 - 16 - 16) (sp - 48 - 16 - 16 - 16) (sp - 48 + 16) (sp - 48 - 16) loc (sp - 48 + 16) 1 1
    lpc (Or.inl ⟨rfl, by decide⟩) S hS (by omega) (by omega) (by omega) (by omega) (by omega) Ga G'
    iprop(expectArgs n (sp - 48) m l ∗ D1) Kg K bs hpos hlen hutf h hfit hov $$ [H817 F826 Sg Hts]
  · iframe H817 F826 Sg Hts
  ihave #S817' := Spec817_mono cfg lim (d + 4) inst mi Cg n g gt (sp - 48 - 16 - 16 - 16)
    (sp - 48 - 16 - 16 - 16) (sp - 48 + 16) (sp - 48 - 16) loc
    iprop(n ↦[i32][ (sp - 48 - 16).toNat + 8 ] (sp - 48 + 16) ∗
      (argsHead n (sp - 48 + 16) 1 1 ∗ expectArgs n (sp - 48) m l ∗
        (stk n ((sp - 48 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗ Ga ∗
          envP n ta A lpc 1066360 179 (A 826) D1 h)))
    _ _ h bs (by
      iintro ⟨I8, HA, EA, Hs, HGa, HE⟩
      iunfold envP at HE
      icases HE with ⟨HH, Vg, Tg, HD1, HI, HS, Hh⟩
      iframe I8 HA Hs HGa
      iunfold envP
      iframe HH Vg Tg HD1 HI HS Hh EA) $$ S817
  iapply (f879_spec cfg lim d type inst mi A n g ta hm (by omega) Cg gt sp m l loc (by omega) hloc
    iprop(stk n ((sp - 48 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗ Ga ∗
      envP n ta A lpc 1066360 179 (A 826) D1 h) (cost817 cfg f826 Kg K bs h) h bs)
  iframe H859 F859 S817'

set_option maxRecDepth 100000 in
/-- **`core::panicking::panic(m, l, loc)`** (853) down to the hook's trap: with the near-sdk hook
installed, the host panicked with the bytes `to_string` writes on the `PanicInfo`
`(payload StrPanicPayload((m, l)), message Some(Arguments { pieces: [(m, l)], args: [] }), loc)`. -/
theorem f853_full (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (sp m l loc lpc : UInt32) (hloc : loc ≠ 0) (S : Nat) (hS : 32 ≤ S) (hsp : S + 160 ≤ sp.toNat)
    (hal : sp.toNat % 8 = 0) (D1 : IProp GF) (K : Nat) (bs : List UInt8)
    (hpos : 0 < bs.length) (hlen : bs.length < 2 ^ 32) (hutf : validUtf8 bs = true) (h : NearState)
    (hfit : LogFits h bs.length) (hov : h.extCosts.cost "read_memory_byte" * bs.length < 2 ^ 64) :
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
      A 828 ↪[wf] FuncInst.wasm types[14]! inst f828 ∗
      ToStr cfg lim (d + 8) inst mi Cg n g gt (sp - 32 - 16 - 16 - 16 - 16 - 32 - 32)
        (sp - 32 - 16 - 16 - 16 - 16 - 32 + 16) S
        iprop(infoCells n (sp - 32 - 16 - 16 - 16 - 16 - 32 + 16) (sp - 32 - 16 - 16 - 16 - 16) 1066416
            (sp - 32) loc ∗
          (n ↦[i32][ (sp - 32 - 16 - 16 - 16 - 16).toNat ] m ∗
            n ↦[i32][ (sp - 32 - 16 - 16 - 16 - 16).toNat + 4 ] l) ∗
          (n ↦[i32][ (sp - 32 - 16).toNat + 8 ] (sp - 32) ∗ argsHead n (sp - 32) 1 0 ∗
            n ↦[i32][ (sp - 32).toNat ] (sp - 32 + 24) ∗ n ↦[i32][ (sp - 32 + 24).toNat ] m ∗
            n ↦[i32][ (sp - 32 + 24).toNat + 4 ] l ∗
            iprop(n ↦[i32][ (sp - 32).toNat + 8 ] 0 ∗ n ↦[i32][ (sp - 32).toNat + 16 ] 1067136 ∗ D1))) K bs
      ⊢ MFunSpecT (GF := GF) cfg lim d type inst mi f853 Cg
        (fun args => iprop(⌜args = [.i32 m, .i32 l, .i32 loc]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 80) 80 ∗
          (stk n ((sp - 32 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗
            envP n ta A lpc 1066380 181 (A 828) D1 h)))
        (fun _ => 180 * cfg.regularOpCost + cost817 cfg f828 (6 * cfg.regularOpCost) K bs h)
        (fun _ _ => iprop(False)) (fun _ => panicked Cg h bs) := by
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h48 : (sp - 32 - 16).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h32] <;> omega
  have h64 : (sp - 32 - 16 - 16).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have h80 : (sp - 32 - 16 - 16 - 16).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h64] <;> omega
  have e24 : (sp - 32 + 24).toNat = (sp - 32).toNat + 24 := by simp [UInt32.toNat_add]; omega
  iintro ⟨#H859, #F859, #H817, #F828, #Hts⟩
  ihave #S817 := f817_str cfg lim (d + 4) inst mi e A n g ta mx hm (by omega) Cg gt
    (sp - 32 - 16 - 16 - 16) (sp - 32 - 16 - 16 - 16) (sp - 32) (sp - 32 - 16) loc (sp - 32) (sp - 32 + 24)
    m l lpc S hS (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    iprop(n ↦[i32][ (sp - 32).toNat + 8 ] 0 ∗ n ↦[i32][ (sp - 32).toNat + 16 ] 1067136 ∗ D1) K bs hpos
    hlen hutf h hfit hov $$ [H817 F828 Hts]
  · iframe H817 F828 Hts
  ihave #S817' := Spec817_mono cfg lim (d + 4) inst mi Cg n g gt (sp - 32 - 16 - 16 - 16)
    (sp - 32 - 16 - 16 - 16) (sp - 32) (sp - 32 - 16) loc
    iprop(n ↦[i32][ (sp - 32 - 16).toNat + 8 ] (sp - 32) ∗
      (argsHead n (sp - 32) 1 0 ∗ strArgs n (sp - 32) m l ∗
        (stk n ((sp - 32 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗
          envP n ta A lpc 1066380 181 (A 828) D1 h)))
    _ _ h bs (by
      iintro ⟨I8, HA, SA, Hs, HE⟩
      iunfold strArgs at SA
      icases SA with ⟨S0, S8, S16, S24, S28⟩
      iunfold envP at HE
      icases HE with ⟨HH, Vg, Tg, HD1, HI, HS, Hh⟩
      ihave S24 := memBytes_congr (j := (sp - 32 + 24).toNat) (by omega) |>.1 $$ S24
      ihave S28 := memBytes_congr (j := (sp - 32 + 24).toNat + 4) (by omega) |>.1 $$ S28
      iframe I8 HA Hs S0 S24 S28
      iunfold envP
      iframe HH Vg Tg HD1 HI HS Hh S8 S16) $$ S817
  iapply (f853_spec cfg lim d type inst mi A n g ta hm (by omega) Cg gt sp m l loc (by omega) hloc
    iprop(stk n ((sp - 32 - 16 - 16 - 16).toNat - 80 - S) (S + 80) ∗
      envP n ta A lpc 1066380 181 (A 828) D1 h) (cost817 cfg f828 (6 * cfg.regularOpCost) K bs h) h bs)
  iframe H859 F859 S817'

end Spec

end WNear.Binary.PanicEntries
