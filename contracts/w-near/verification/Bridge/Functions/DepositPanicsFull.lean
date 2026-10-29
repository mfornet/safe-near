import Bridge.Functions.DepositPanicSpec
import Bridge.Functions.PanicBeginFull
import Bridge.Functions.PanicFmtFull
import Bridge.Methods.NearDepositPanics

/-!
# `near_deposit`'s panics through the Rust hook, discharged (M8)

The three `PanicSpecD` premises of 232's body, from `PanicBeginFull.f664_requiresPositive`,
`f664_depositTooSmall` and `PanicFmtFull.f879_totalSupplyOverflow`:

* `dPos`, `dSmall`, `dSup`: the static data each site's `to_string` reads (the message, the
  `Location`, the file name, the `Display` pieces and table slots); `dAll`: their non-separating
  conjunction (only one panic happens on a run, and all three come from the same cells);
* `codePanics`: the code the three sites run;
* `kPos`, `kSmall`, `kSup`: the costs, on what the costs read of the host (`hostK`);
* `spec664pos`, `spec664small`, `spec879sup`.

The texts are the model's messages (`NearDepositPanics.textPositive` …, `textPos_eq` …).
-/

namespace WNear.Binary.DepositPanicsFull

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod iface)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.PanicStr (panicSlot panicked)
open WNear.Binary.PanicBegin (panicCode' env cost664 cost662 cost663)
open WNear.Binary.PanicText (panicText wnearRs requiresPositive depositTooSmall totalSupplyOverflow coreImplRs)
open WNear.Binary.ToStrPay (toStrEnv codeTS costTS XP')
open WNear.Binary.ToStrMsg (codeTSM)
open WNear.Binary.GetFmt (getData code826)
open WNear.Binary.PanicFmt (code817 code859 envP)
open WNear.Binary.PanicFmtFull (hookEnvM cost879)
open WNear.Binary.DepositPanicSpec (hookRes pPre PanicSpecD MFunSpecT_persistent)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.PanicDisplay (pk12 pptrA plenA pptrB plenB qp qcp colon XB)

theorem textPos_eq : panicText requiresPositive wnearRs 15 9 = NearDepositPanics.textPositive := by decide +kernel
theorem textSmall_eq : panicText depositTooSmall wnearRs 20 13 = NearDepositPanics.textTooSmall := by
  decide +kernel
theorem textSup_eq : panicText totalSupplyOverflow coreImplRs 108 55 = NearDepositPanics.textSupply := by
  decide +kernel

theorem textPos_length : NearDepositPanics.textPositive.length = 68 := by decide +kernel
theorem textSmall_length : NearDepositPanics.textTooSmall.length = 56 := by decide +kernel
theorem textSup_length : NearDepositPanics.textSupply.length = 163 := by decide +kernel

/-- A host with the fee tables of `k` (what the panics' costs read). -/
def hostK (k : NewBody.Keep) : NearState := { (default : NearState) with extCosts := k.extCosts }

theorem panicUtf8Use_hostK (h : NearState) (m : Nat) :
    panicUtf8Use (hostK (NewBody.keep h)) m = panicUtf8Use h m := by
  simp [panicUtf8Use, chargesUse, panicUtf8Charges, chargeUse, hostK, NewBody.keep]

/-- The costs, on the free cells and the host's fee tables. -/
noncomputable def kPos (cfg : WasmConfig) (F : Nat) (k : NewBody.Keep) : Nat :=
  cost664 cfg (costTS cfg F 5 68) (panicText requiresPositive wnearRs 15 9) (hostK k)
noncomputable def kSmall (cfg : WasmConfig) (F : Nat) (k : NewBody.Keep) : Nat :=
  cost664 cfg (costTS cfg F 5 56) (panicText depositTooSmall wnearRs 20 13) (hostK k)
noncomputable def kSup (cfg : WasmConfig) (F : Nat) (k : NewBody.Keep) : Nat :=
  cost879 cfg F 6 21 (panicText totalSupplyOverflow coreImplRs 108 55) (hostK k)

theorem cost664_keep (cfg : WasmConfig) (K : Nat) (bs : List UInt8) (h : NearState) :
    cost664 cfg K bs (hostK (NewBody.keep h)) = cost664 cfg K bs h := by
  simp only [cost664, cost662, cost663, PanicWithHook.cost824, PanicHook.cost474, panicUtf8Use_hostK]

theorem cost879_keep (cfg : WasmConfig) (F J B : Nat) (bs : List UInt8) (h : NearState) :
    cost879 cfg F J B bs (hostK (NewBody.keep h)) = cost879 cfg F J B bs h := by
  simp only [cost879, PanicFmt.cost817, PanicWithHook.cost824, PanicHook.cost474, panicUtf8Use_hostK]

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem stkA2' {n a b k k' : Nat} (h : a = b) (hk : k = k') : stk (GF := GF) n a k ⊢ stk n b k' := by
  subst h hk; exact .rfl

theorem MFunSpecT_pre {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {P P' : List Value → IProp GF} {K K' : List Value → Nat}
    {Q : List Value → List Value → IProp GF} {T : List Value → IProp GF} (hP : ∀ args, P' args ⊢ P args)
    (hK : ∀ args, K' args = K args) :
    MFunSpecT cfg lim d type inst mi code Cg P K Q T ⊢ MFunSpecT cfg lim d type inst mi code Cg P' K' Q T := by
  unfold MFunSpecT
  iintro #H
  imodintro
  iintro %args %R HP Hc
  rw [hK]
  iapply H $$ %args %R [HP] Hc
  iapply hP $$ HP

/-- `PanicDisplay.XB` without the digit table (`pPre` passes it separately). -/
def XBm (n : Nat) (loc file flen line col : UInt32) (fileB : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ 1070704 ] colon ∗
    (n ↦[i32][ loc.toNat ] file ∗ n ↦[i32][ loc.toNat + 4 ] flen ∗ n ↦[i32][ loc.toNat + 8 ] line ∗
      n ↦[i32][ loc.toNat + 12 ] col) ∗ n ↦[wms][ file.toNat ] fileB)

theorem XB_of (n : Nat) (loc file flen line col : UInt32) (fileB : List UInt8) :
    XBm (GF := GF) n loc file flen line col fileB ∗ n ↦[wms][ 1070974 ] FmtDigits.lut ⊢
      XB n loc file flen line col fileB := by
  iintro ⟨H, L⟩
  iunfold XBm at H
  icases H with ⟨C, W, F⟩
  iunfold XB
  iframe C L W F

/-- `ToStrPay.XP'` without the digit table. -/
def XPm (n ta : Nat) (A : Nat → Nat) (m loc file flen line col : UInt32) (msg fileB : List UInt8) :
    IProp GF :=
  iprop(n ↦[wms][ 1070672 ] pk12 ∗ (n ↦[i32][ 1062988 + 12 ] 139 ∗ ta ↦[wt][ 139 ] Ref.func (A 661)) ∗
    ((n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 ] pptrA 0 ∗
        n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 + 4 ] plenA 0) ∗
      (n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 ] pptrA 1 ∗
        n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 + 4 ] plenA 1) ∗
      ta ↦[wt][ (201 : UInt32).toNat ] Ref.func (A 886)) ∗
    ((n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 ] pptrB 0 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 + 4 ] plenB 0) ∗
      (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 ] pptrB 1 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 + 4 ] plenB 1) ∗
      (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 ] pptrB 2 ∗
        n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 + 4 ] plenB 2) ∗
      ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880) ∗ ta ↦[wt][ (3 : UInt32).toNat ] Ref.func (A 870)) ∗
    (n ↦[wms][ 1070684 ] qp ∗ n ↦[wms][ 1070685 ] qcp) ∗ n ↦[wms][ m.toNat ] msg ∗
    XBm n loc file flen line col fileB)

theorem XP_of_m (n ta : Nat) (A : Nat → Nat) (m loc file flen line col : UInt32) (msg fileB : List UInt8) :
    XPm (GF := GF) n ta A m loc file flen line col msg fileB ∗ n ↦[wms][ 1070974 ] FmtDigits.lut ⊢
      XP' n ta A m loc file flen line col msg fileB := by
  iintro ⟨H, L⟩
  iunfold XPm at H
  icases H with ⟨H1, H2, H3, H4, H5, H6, H7⟩
  ihave H7 := XB_of n loc file flen line col fileB $$ [H7 L]
  · iframe H7 L
  iunfold XP'
  iframe H1 H2 H3 H4 H5 H6 H7

/-- `PanicFmtFull.hookEnvM` without the digit table. -/
def hookEnvMm (n ta : Nat) (A : Nat → Nat) (loc file flen line col : UInt32) (fileB : List UInt8) : IProp GF :=
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
    XBm n loc file flen line col fileB ∗
    (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759) ∗
      ta ↦[wt][ (104 : UInt32).toNat ] Ref.func (A 469)) ∗
    (n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 ] 1054332 ∗ n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 + 4 ] 0))

theorem hookEnvM_of_m (n ta : Nat) (A : Nat → Nat) (loc file flen line col : UInt32) (fileB : List UInt8) :
    hookEnvMm (GF := GF) n ta A loc file flen line col fileB ∗ n ↦[wms][ 1070974 ] FmtDigits.lut ⊢
      hookEnvM n ta A loc file flen line col fileB := by
  iintro ⟨H, L⟩
  iunfold hookEnvMm at H
  icases H with ⟨H1, H2, H3, H4, H5, H6, H7⟩
  ihave H5 := XB_of n loc file flen line col fileB $$ [H5 L]
  · iframe H5 L
  iunfold hookEnvM
  iframe H1 H2 H3 H4 H5 H6 H7

/-- The data `begin_panic`'s `to_string` reads at a `require!` of `near_deposit`, past the heap and
the digit table. -/
def d664 (n ta : Nat) (A : Nat → Nat) (m loc line col : UInt32) (msg : List UInt8) : IProp GF :=
  iprop(XPm n ta A m loc 1050526 13 line col msg wnearRs ∗
    (n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func (A 759) ∗
      ta ↦[wt][ (104 : UInt32).toNat ] Ref.func (A 469)) ∗
    (n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 ] 1054332 ∗ n ↦[i32][ (1054332 : UInt32).toNat + 8 * 0 + 4 ] 0))

def dPos (n ta : Nat) (A : Nat → Nat) : IProp GF := d664 n ta A 1050492 1050540 15 9 requiresPositive
def dSmall (n ta : Nat) (A : Nat → Nat) : IProp GF := d664 n ta A 1050556 1050580 20 13 depositTooSmall

/-- The data `expect_failed`'s payload `get` and `to_string` read for the supply overflow. -/
def dSup (n ta : Nat) (A : Nat → Nat) : IProp GF :=
  iprop(getData n ta A 1053016 totalSupplyOverflow ∗ hookEnvMm n ta A 1053040 1052816 119 108 55 coreImplRs)

/-- All three, one of which a run uses. -/
def dAll (n ta : Nat) (A : Nat → Nat) : IProp GF := iprop(dPos n ta A ∧ dSmall n ta A ∧ dSup n ta A)

/-- The code the three panics run (persistent). -/
def codePanics (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(A 662 ↪[wf] FuncInst.wasm types[0]! inst f662 ∗ A 663 ↪[wf] FuncInst.wasm types[0]! inst f663 ∗
    A 888 ↪[wf] FuncInst.wasm types[32]! inst f888 ∗ panicCode' e inst mi A n mx ∗ codeTS n maxP inst mi A ∗
    code859 inst mi A ∗ A 859 ↪[wf] FuncInst.wasm types[14]! inst f859 ∗ code817 e inst mi A n mx ∗
    A 826 ↪[wf] FuncInst.wasm types[14]! inst f826 ∗ code826 n maxP inst mi A ∗ codeTSM n maxP inst mi A)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (codePanics (GF := GF) e inst mi A n maxP mx) := by
  unfold codePanics; infer_instance

theorem hookRes_split (n ta : Nat) (A : Nat → Nat) (lpc : UInt32) :
    hookRes (GF := GF) n ta A lpc ⊢ PanicWithHook.hookInstalled n ta A lpc ∗ n ↦[i32][ 1062968 + 16 ] 137 ∗
      ta ↦[wt][ 137 ] Ref.func (A 679) ∗ n ↦[i32][ (1066360 : UInt32).toNat + 16 ] 179 ∗
      ta ↦[wt][ (179 : UInt32).toNat ] Ref.func (A 826) := by
  iintro H
  iunfold hookRes at H
  rw [show (1066360 : UInt32).toNat = 1066360 from rfl, show (179 : UInt32).toNat = 179 from rfl]
  iexact H

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`require!(deposit > 0)`**'s panic, discharged. -/
theorem spec664pos (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (e : Nat)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (lpc : UInt32) (maxP SP : Nat) (hSP : 608 ≤ SP) :
    PanicSpecD (GF := GF) cfg lim inst mi (codePanics e inst mi A n maxP mx) n g ta A gt lpc maxP f664 SP
      (dAll n ta A) 35 1050492 34 1050540 (kPos cfg) NearDepositPanics.textPositive := by
  intro d Cg sp h hl live F idx hd hsp hal hsp2 hroom hF hfit hov
  obtain ⟨r1, r2, r3, r4⟩ := hroom
  rw [textPos_length] at hfit hov
  have S := PanicBeginFull.f664_requiresPositive (GF := GF) cfg lim d types[31]! inst mi e A n g ta mx hm
    (by omega) Cg gt sp lpc idx (SP - 112) (by omega) (by omega) (by omega) hal maxP hl hl live F hF (by omega)
    (by omega) r1 r2 le_rfl iprop(emp) h hfit hov
  simp only [textPos_eq] at S
  iintro #HC
  iunfold codePanics at HC
  icases HC with ⟨#F662, #F663, #F888, #HPC, #HTS, -, -, -, -, -, -⟩
  ihave #S' := S $$ [F662 F663 F888 HPC HTS]
  · iframe F662 F663 F888 HPC HTS
  iapply MFunSpecT_pre (P := _) (K := _) ?_ ?_ $$ S'
  · intro args
    iintro ⟨%ha, HP⟩
    iunfold pPre at HP
    icases HP with ⟨Hg, Hs, HH, HI, HPS, Hinv, Hvt, HD, HLut, Hh⟩
    icases hookRes_split n ta A lpc $$ HH with ⟨HH, H137, T137, -, -⟩
    iunfold dAll at HD
    icases HD with ⟨HD, -⟩
    iunfold dPos, d664 at HD
    icases HD with ⟨HX, H157, H1054⟩
    ihave HX := XP_of_m n ta A 1050492 1050540 1050526 13 15 9 requiresPositive wnearRs $$ [HX HLut]
    · iframe HX HLut
    iframe Hg
    isplitr
    · ipureintro; exact ha
    isplitl [Hs]
    · iapply stkA2' (by omega) (by omega) $$ Hs
    iunfold env
    iframe HH H137 T137 HI HPS Hh
    iunfold toStrEnv
    iframe HX Hvt Hinv H157 H1054
  · intro args
    simp only [kPos, cost664_keep, textPos_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`require!(deposit >= min)`**'s panic, discharged. -/
theorem spec664small (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (e : Nat)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (lpc : UInt32) (maxP SP : Nat) (hSP : 608 ≤ SP) :
    PanicSpecD (GF := GF) cfg lim inst mi (codePanics e inst mi A n maxP mx) n g ta A gt lpc maxP f664 SP
      (dAll n ta A) 35 1050556 21 1050580 (kSmall cfg) NearDepositPanics.textTooSmall := by
  intro d Cg sp h hl live F idx hd hsp hal hsp2 hroom hF hfit hov
  obtain ⟨r1, r2, r3, r4⟩ := hroom
  rw [textSmall_length] at hfit hov
  have S := PanicBeginFull.f664_depositTooSmall (GF := GF) cfg lim d types[31]! inst mi e A n g ta mx hm
    (by omega) Cg gt sp lpc idx (SP - 112) (by omega) (by omega) (by omega) hal maxP hl hl live F hF (by omega)
    (by omega) r1 r2 le_rfl iprop(emp) h hfit hov
  simp only [textSmall_eq] at S
  iintro #HC
  iunfold codePanics at HC
  icases HC with ⟨#F662, #F663, #F888, #HPC, #HTS, -, -, -, -, -, -⟩
  ihave #S' := S $$ [F662 F663 F888 HPC HTS]
  · iframe F662 F663 F888 HPC HTS
  iapply MFunSpecT_pre (P := _) (K := _) ?_ ?_ $$ S'
  · intro args
    iintro ⟨%ha, HP⟩
    iunfold pPre at HP
    icases HP with ⟨Hg, Hs, HH, HI, HPS, Hinv, Hvt, HD, HLut, Hh⟩
    icases hookRes_split n ta A lpc $$ HH with ⟨HH, H137, T137, -, -⟩
    iunfold dAll at HD
    icases HD with ⟨-, HD, -⟩
    iunfold dSmall, d664 at HD
    icases HD with ⟨HX, H157, H1054⟩
    ihave HX := XP_of_m n ta A 1050556 1050580 1050526 13 20 13 depositTooSmall wnearRs $$ [HX HLut]
    · iframe HX HLut
    iframe Hg
    isplitr
    · ipureintro; exact ha
    isplitl [Hs]
    · iapply stkA2' (by omega) (by omega) $$ Hs
    iunfold env
    iframe HH H137 T137 HI HPS Hh
    iunfold toStrEnv
    iframe HX Hvt Hinv H157 H1054
  · intro args
    simp only [kSmall, cost664_keep, textSmall_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`expect("Total supply overflow")`** in `internal_deposit`, discharged. -/
theorem spec879sup (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (e : Nat)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (lpc : UInt32) (maxP SP : Nat) (hSP : 608 ≤ SP) :
    PanicSpecD (GF := GF) cfg lim inst mi (codePanics e inst mi A n maxP mx) n g ta A gt lpc maxP f879 SP
      (dAll n ta A) 35 1053016 21 1053040 (kSup cfg) NearDepositPanics.textSupply := by
  intro d Cg sp h hl live F idx hd hsp hal hsp2 hroom hF hfit hov
  obtain ⟨r1, r2, r3, r4⟩ := hroom
  rw [textSup_length] at hfit hov
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h64 : (sp - 48 - 16).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h48] <;> omega
  have h80 : (sp - 48 - 16 - 16).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h64] <;> omega
  have h96 : (sp - 48 - 16 - 16 - 16).toNat = sp.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, h80] <;> omega
  have S := PanicFmtFull.f879_totalSupplyOverflow (GF := GF) cfg lim d types[31]! inst mi e A n g ta mx hm
    (by omega) Cg gt sp lpc idx (SP - 176) (by omega) (by omega) (by omega) hal maxP hl (hl + 65536) live F hF
    (by omega) (by omega) r1 r2 le_rfl iprop(emp) h hfit hov
  simp only [textSup_eq] at S
  iintro #HC
  iunfold codePanics at HC
  icases HC with ⟨-, -, -, -, -, #H859c, #F859, #H817, #F826, #H826c, #HTSM⟩
  ihave #S' := S $$ [H859c F859 H817 F826 H826c HTSM]
  · iframe H859c F859 H817 F826 H826c HTSM
  iapply MFunSpecT_pre (P := _) (K := _) ?_ ?_ $$ S'
  · intro args
    iintro ⟨%ha, HP⟩
    iunfold pPre at HP
    icases HP with ⟨Hg, Hs, HH, HI, HPS, Hinv, Hvt, HD, HLut, Hh⟩
    icases hookRes_split n ta A lpc $$ HH with ⟨HH, -, -, H179, T179⟩
    iunfold dAll at HD
    icases HD with ⟨-, -, HD⟩
    iunfold dSup at HD
    icases HD with ⟨HGD, HEM⟩
    ihave HEM := hookEnvM_of_m n ta A 1053040 1052816 119 108 55 coreImplRs $$ [HEM HLut]
    · iframe HEM HLut
    icases BorshFT.stkSp (SP - 96) 96 (by omega) $$ Hs with ⟨Lo, Up⟩
    iframe Hg
    isplitr
    · ipureintro; exact ha
    isplitl [Up]
    · iapply stkA2' (by omega) (by omega) $$ Up
    isplitl [Lo]
    · iapply stkA2' (by omega) (by omega) $$ Lo
    iframe HGD Hvt Hinv
    iunfold envP
    iframe HH H179 T179 HEM HI HPS Hh
  · intro args
    simp only [kSup, cost879_keep, textSup_eq]

end Spec

end WNear.Binary.DepositPanicsFull
