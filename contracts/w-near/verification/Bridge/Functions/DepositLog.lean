import Bridge.Functions.StrSinkMulti
import Bridge.Functions.FmtStrPad
import Bridge.Functions.FmtDisplay
import Bridge.Functions.FmtString

/-!
# `core::fmt::write` (872) on `near_deposit`'s log (M8)

`near_deposit` (232) logs `format!("Deposit {} NEAR to {}", amount, account_id)`: 846 calls 872 on

```
Arguments { pieces: [("Deposit ", 8), (" NEAR to ", 9)] at 1050632, fmt: None,
            args: [(&amount, 5), (&account_id, 6)] }
```

with the sink `(dp, 1066728)`: `*dp` the `String` of `format!` (`StrSinkMulti.ssink`), whose
`write_str` is table entry 189 (840). The arguments' formatters are table entries 5
(`<u128 as Display>::fmt`, 901) and 6 (`<String as Display>::fmt`, 179).

The writes, `St 0 → … → St 4` (`lSt`): the piece `"Deposit "` (`piece_w`), the `u128`'s decimal
digits (`arg_u128`, 901 on `ssink_w` as `fmt_u128`'s sink), the piece `" NEAR to "`, the account's
bytes (`arg_str`, 179 through `pad`). `f872_log` is `FmtWriteN.f872_gen` on them (`hyp872_log`).

Below 872's frame `s' = s - 48`, the writes use 192 bytes of stack: 901's frame (144) and the
sink's (48).
-/

namespace WNear.Binary.DepositLog

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.StrSinkGrow (strCode)
open WNear.Binary.StrSinkMulti (ssink ssink_w costS memcpy_mono)
open WNear.Binary.FmtWriteN (fmtrP argsN Hyp872 f872_gen costN)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtU128 (sinkSpec val)
open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDisplay (fmtCode f901_spec)
open WNear.Binary.FmtStrPad (strW f179_spec cost179)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

/-! ## The text -/

/-- `"Deposit "`. -/
def pDeposit : List UInt8 := [68, 101, 112, 111, 115, 105, 116, 32]
/-- `" NEAR to "`. -/
def pNear : List UInt8 := [32, 78, 69, 65, 82, 32, 116, 111, 32]

theorem pDeposit_eq : pDeposit = "Deposit ".toUTF8.toList := by decide +kernel
theorem pNear_eq : pNear = " NEAR to ".toUTF8.toList := by decide +kernel

/-- The text after `i` writes: the digits `ds` of the amount, the account's bytes `ab`. -/
def logW (ds ab : List UInt8) : Nat → List UInt8
  | 0 => []
  | 1 => pDeposit
  | 2 => pDeposit ++ ds
  | 3 => (pDeposit ++ ds) ++ pNear
  | _ => ((pDeposit ++ ds) ++ pNear) ++ ab

theorem logW_length (ds ab : List UInt8) (i : Nat) : (logW ds ab i).length ≤ 17 + ds.length + ab.length := by
  unfold logW
  split <;> simp [pDeposit, pNear] <;> omega

/-! ## The pieces and the arguments -/

/-- The pieces' addresses and lengths. -/
def pptr (j : Nat) : UInt32 := if j = 0 then 1050612 else 1050620
def plen (j : Nat) : UInt32 := if j = 0 then 8 else 9

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The cost of a piece's write. -/
noncomputable abbrev Ka (cfg : WasmConfig) (F : Nat) : Nat := costS cfg F 120 9

theorem costS_mono (cfg : WasmConfig) (F B : Nat) {k k' : Nat} (h1 : 0 < k) (h : k ≤ k') :
    costS cfg F B k ≤ costS cfg F B k' := by
  have := Nat.mul_le_mul_right cfg.regularOpCost (memcpy_mono h1 h)
  unfold costS; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **A piece's write** (840 on `ssink`), the bytes `sb` at `p` taken from `X` (`hX`): from the
stack pointer `s'` with 192 bytes below it. -/
theorem piece_w (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (maxP L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (v aidx : UInt32)
    (hL1 : L0 + 3 * 65536 ≤ 2 ^ 32) (hL2 : L0 + 2 * 65536 ≤ maxP * 65536) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (s dp p k : UInt32) (w w' sb : List UInt8) (hs : 192 ≤ s.toNat) (hsb : sb.length = k.toNat)
    (hk : 0 < k.toNat) (hk9 : k.toNat ≤ 9)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hwB : w.length + k.toNat ≤ 120) (hw' : w' = w ++ sb)
    (X : IProp GF) (hX : X ⊢ n ↦[wms][ p.toNat ] sb ∗ (n ↦[wms][ p.toNat ] sb -∗ X)) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d types[15]! inst mi f840 Cg
        (fun args => iprop(⌜args = [.i32 dp, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          (stk n (s.toNat - 192) 192 ∗ ssink n maxP L0 live F 34 120 v aidx ta (A 578) w ∗
            n ↦[i32][ dp.toNat ] v ∗ X)))
        (fun _ => Ka cfg F)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          (stk n (s.toNat - 192) 192 ∗ ssink n maxP L0 live F 34 120 v aidx ta (A 578) w' ∗
            n ↦[i32][ dp.toNat ] v ∗ X))) := by
  subst hw'
  have S := ssink_w (GF := GF) cfg lim d types[15]! rfl inst mi A n g ta hm hd Cg gt maxP L0 live F 34 120 v aidx
    (by decide) (by decide) (by decide) hL1 hL2 hv s dp p k w sb (by omega) hsb hp hwB
  refine S.trans ((MFunSpec_frame (Fr := iprop(stk n (s.toNat - 192) 144 ∗
      (n ↦[wms][ p.toNat ] sb -∗ X))) ?_ ?_).trans (MFunSpec_cost ?_))
  · intro args
    iintro ⟨%ha, Hg, Hs, HS, Hd, HX⟩
    icases hX $$ HX with ⟨Hp, HX⟩
    icases stkSp 144 48 rfl $$ Hs with ⟨Hs1, Hs2⟩
    iframe Hs1 HX Hg Hd HS Hp
    isplitr; · ipureintro; exact ha
    iapply stkA (by omega) $$ Hs2
  · intro args rs
    iintro ⟨⟨Hs1, HX⟩, %hrs, Hg, Hs2, Hd, HS, Hp⟩
    iframe Hg Hd HS
    isplitr; · ipureintro; exact hrs
    isplitl [Hs1 Hs2]
    · iapply stkJ (a := s.toNat - 192) (b := s.toNat - 48) (k1 := 144) (k2 := 48) (by omega) rfl
      iframe Hs1 Hs2
    iapply HX $$ Hp
  · intro _
    exact costS_mono cfg F 120 hk hk9

/-- The cost of the `u128` argument (901 on `ssink`), the activation excluded. -/
noncomputable def K901 (cfg : WasmConfig) (F : Nat) (lo hi : UInt64) : Nat :=
  23 * cfg.regularOpCost + (FmtU128.cost lo hi * cfg.regularOpCost +
    activationGas cfg.regularOpCost (entryLocals f840 [.i32 0, .i32 0, .i32 0]) +
      costS cfg F 120 (decDigits (val lo hi)).length)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `ssink_w` as `fmt_u128`'s sink (`sinkSpec`), at the stack pointer `sp`. -/
theorem sink_u128 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (maxP L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (v aidx : UInt32)
    (hL1 : L0 + 3 * 65536 ≤ 2 ^ 32) (hL2 : L0 + 2 * 65536 ≤ maxP * 65536) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (sp dp : UInt32) (lo hi : UInt64) (w : List UInt8) (hs : 48 ≤ sp.toNat) (hs2 : sp.toNat + 144 ≤ 2 ^ 32)
    (hwB : w.length + (decDigits (val lo hi)).length ≤ 120) :
    strCode n maxP inst mi A
      ⊢ sinkSpec (GF := GF) cfg lim d inst mi n g gt sp (UInt32.ofNat (39 - (decDigits (val lo hi)).length)) dp f840
          (decDigits (val lo hi))
          iprop(stk n (sp.toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗ ssink n maxP L0 live F 34 120 v aidx ta (A 578) w)
          iprop(stk n (sp.toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
            ssink n maxP L0 live F 34 120 v aidx ta (A 578) (w ++ decDigits (val lo hi)))
          (costS cfg F 120 (decDigits (val lo hi)).length) Cg := by
  iintro #Hk
  iunfold sinkSpec
  imodintro
  iintro %p %k %⟨hp, hk⟩
  have hL := FmtString.decDigits_le lo hi
  have hc : (UInt32.ofNat (39 - (decDigits (val lo hi)).length)).toNat = 39 - (decDigits (val lo hi)).length := by
    simp; omega
  have hk' : k.toNat = (decDigits (val lo hi)).length := by omega
  have S := ssink_w (GF := GF) cfg lim d types[15]! rfl inst mi A n g ta hm hd Cg gt maxP L0 live F 34 120 v aidx
    (by decide) (by decide) (by decide) hL1 hL2 hv sp dp p k w (decDigits (val lo hi)) hs hk'.symm (by omega) (by omega)
  rw [hk'] at S
  ihave HS := S $$ Hk
  iapply (MFunSpec_frame (Fr := iprop(emp)) ?_ ?_) $$ HS
  · intro args
    iintro ⟨%ha, Hg, Hds, Hs, Hd, HS⟩
    iframe Hg Hs Hd HS Hds
    ipureintro; exact ha
  · intro args rs
    iintro ⟨-, %hrs, Hg, Hs, Hd, HS, Hds⟩
    iframe Hg Hs Hd HS Hds
    ipureintro; exact hrs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The `u128` argument** (901, table entry 5): its decimal digits written to `ssink`, from the
stack pointer `s'` with 192 bytes below it. -/
theorem arg_u128 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (maxP L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (v aidx : UInt32)
    (hL1 : L0 + 3 * 65536 ≤ 2 ^ 32) (hL2 : L0 + 2 * 65536 ≤ maxP * 65536) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (s dp u : UInt32) (lo hi : UInt64) (w : List UInt8) (hs : 192 ≤ s.toNat) (hs2 : s.toNat + 48 ≤ 2 ^ 32)
    (hu : u.toNat + 16 ≤ 2 ^ 32) (hwB : w.length + (decDigits (val lo hi)).length ≤ 120) (Y : IProp GF) :
    strCode n maxP inst mi A ∗ fmtCode inst mi A (A 840) f840
      ⊢ MFunSpec (GF := GF) cfg lim d types[13]! inst mi f901 Cg
        (fun args => iprop(⌜args = [.i32 u, .i32 (s + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          fmtrP n ta (s + 8) dp 1066728 189 (A 840) ∗
          (stk n (s.toNat - 192) 192 ∗ ssink n maxP L0 live F 34 120 v aidx ta (A 578) w ∗
            n ↦[i32][ dp.toNat ] v ∗ ((n ↦[wms][ u.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut) ∗ Y))))
        (fun _ => K901 cfg F lo hi)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          fmtrP n ta (s + 8) dp 1066728 189 (A 840) ∗
          (stk n (s.toNat - 192) 192 ∗ ssink n maxP L0 live F 34 120 v aidx ta (A 578) (w ++ decDigits (val lo hi)) ∗
            n ↦[i32][ dp.toNat ] v ∗ ((n ↦[wms][ u.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut) ∗ Y)))) := by
  iintro ⟨#Hsc, #Hfc⟩
  have hlt := s.toNat_lt
  have h144 : (s - 144).toNat = s.toNat - 144 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hf : (s + 8).toNat = s.toNat + 8 := by rw [UInt32.toNat_add]; simp; omega
  ihave #Sw := sink_u128 cfg lim (d + 3) inst mi A n g ta hm (by omega) Cg gt maxP L0 live F v aidx hL1 hL2 hv
    (s - 144) dp lo hi w (by omega) (by omega) hwB $$ Hsc
  ihave #S901 := f901_spec (GF := GF) cfg lim d types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt lo hi u s
    (s + 8) dp 1066728 189 hu (by omega) (by omega) (by decide) (A 840) f840
    iprop(stk n ((s - 144).toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
      ssink n maxP L0 live F 34 120 v aidx ta (A 578) w)
    iprop(stk n ((s - 144).toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
      ssink n maxP L0 live F 34 120 v aidx ta (A 578) (w ++ decDigits (val lo hi)))
    (costS cfg F 120 (decDigits (val lo hi)).length) $$ [Hfc Sw]
  · iframe Hfc Sw
  iunfold K901
  iapply (MFunSpec_frame (Fr := iprop(n ↦[i32][ (s + 8).toNat + 16 ] 0 ∗ Y)) ?_ ?_) $$ S901
  · intro args
    iintro ⟨%ha, Hg, HF, Hs, HS, Hd, ⟨Hu, Hl⟩, HY⟩
    iunfold fmtrP at HF
    icases HF with ⟨HF, Hp⟩
    icases stkSp 48 144 rfl $$ Hs with ⟨Hs1, Hs2⟩
    iframe Hp HY Hu
    isplitr; · ipureintro; exact ha
    iunfold FmtU128.pre
    iframe Hg HF Hl HS Hd
    isplitr; · ipureintro; rfl
    isplitl [Hs2]
    · iapply stkA (by omega) $$ Hs2
    iapply stkA (by omega) $$ Hs1
  · intro args rs
    iintro ⟨⟨Hp, HY⟩, Hu, HQ⟩
    iunfold FmtU128.post at HQ
    icases HQ with ⟨%hrs, Hg, Hs2, Hl, HF, Hs1, Hd, HS⟩
    iframe Hg Hd HS HY Hu Hl
    isplitr; · ipureintro; exact hrs
    isplitl [HF Hp]
    · iunfold fmtrP; iframe HF Hp
    iapply stkJ (a := s.toNat - 192) (b := s.toNat - 144) (k1 := 48) (k2 := 144) (by omega) rfl
    isplitl [Hs1]
    · iapply stkA (by omega) $$ Hs1
    iexact Hs2

/-- The code of the `String` argument (persistent). -/
def strArgCode (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗
    A 923 ↪[wf] FuncInst.wasm types[15]! inst f923 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
    A 840 ↪[wf] FuncInst.wasm types[15]! inst f840)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (strArgCode (GF := GF) inst mi A) := by
  unfold strArgCode; infer_instance

/-- The cost of the `String` argument (179 on `ssink`), the activation excluded. -/
noncomputable def K179 (cfg : WasmConfig) (F : Nat) (alen : UInt32) : Nat :=
  cost179 cfg f840 (costS cfg F 120 alen.toNat)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The `String` argument** (179, table entry 6): the `alen` bytes `ab` of the `String` at `sv`
written to `ssink` through `pad`, from the stack pointer `s'` with 192 bytes below it. -/
theorem arg_str (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (maxP L0 : Nat) (live : List (Nat × Nat)) (F : Nat) (v aidx : UInt32)
    (hL1 : L0 + 3 * 65536 ≤ 2 ^ 32) (hL2 : L0 + 2 * 65536 ≤ maxP * 65536) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (s dp sv aptr acap alen : UInt32) (w ab : List UInt8) (hs : 192 ≤ s.toNat) (hs2 : s.toNat + 48 ≤ 2 ^ 32)
    (hab : ab.length = alen.toNat) (hap : aptr.toNat + alen.toNat ≤ 2 ^ 32) (hwB : w.length + alen.toNat ≤ 120)
    (Y : IProp GF) :
    strCode n maxP inst mi A ∗ strArgCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d types[13]! inst mi f179 Cg
        (fun args => iprop(⌜args = [.i32 sv, .i32 (s + 8)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          fmtrP n ta (s + 8) dp 1066728 189 (A 840) ∗
          (stk n (s.toNat - 192) 192 ∗ ssink n maxP L0 live F 34 120 v aidx ta (A 578) w ∗
            n ↦[i32][ dp.toNat ] v ∗ ((strW n sv aptr acap alen ∗ n ↦[wms][ aptr.toNat ] ab) ∗ Y))))
        (fun _ => K179 cfg F alen)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          fmtrP n ta (s + 8) dp 1066728 189 (A 840) ∗
          (stk n (s.toNat - 192) 192 ∗ ssink n maxP L0 live F 34 120 v aidx ta (A 578) (w ++ ab) ∗
            n ↦[i32][ dp.toNat ] v ∗ ((strW n sv aptr acap alen ∗ n ↦[wms][ aptr.toNat ] ab) ∗ Y)))) := by
  iintro ⟨#Hsc, #Hk⟩
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hf : (s + 8).toNat = s.toNat + 8 := by rw [UInt32.toNat_add]; simp; omega
  have S := ssink_w (GF := GF) cfg lim (d + 3) types[15]! rfl inst mi A n g ta hm (by omega) Cg gt maxP L0 live F
    34 120 v aidx (by decide) (by decide) (by decide) hL1 hL2 hv (s - 16) dp aptr alen w ab (by omega) hab hap hwB
  ihave HS := S $$ Hsc
  ihave #Sw : MFunSpec cfg lim (d + 3) types[15]! inst mi f840 Cg
      (fun args => iprop(⌜args = [.i32 dp, .i32 aptr, .i32 alen]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 16)⟩ ∗
        (stk n ((s - 16).toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
          ssink n maxP L0 live F 34 120 v aidx ta (A 578) w ∗ n ↦[wms][ aptr.toNat ] ab)))
      (fun _ => costS cfg F 120 alen.toNat)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 16)⟩ ∗
        (stk n ((s - 16).toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
          ssink n maxP L0 live F 34 120 v aidx ta (A 578) (w ++ ab) ∗ n ↦[wms][ aptr.toNat ] ab))) $$ [HS]
  · iapply (MFunSpec_frame (Fr := iprop(emp)) ?_ ?_) $$ HS
    · intro args
      iintro ⟨%ha, Hg, Hs, Hd, HS, Hp⟩
      iframe Hg Hs Hd HS Hp
      ipureintro; exact ha
    · intro args rs
      iintro ⟨-, %hrs, Hg, Hs, Hd, HS, Hp⟩
      iframe Hg Hs Hd HS Hp
      ipureintro; exact hrs
  iunfold strArgCode at Hk
  icases Hk with ⟨#Hi, #H856, #H923, #H779, #H840⟩
  ihave #S179 := f179_spec (GF := GF) cfg lim d types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s sv
    aptr acap alen (s + 8) dp 1066728 189 (by omega) (by omega) (A 840) f840
    iprop(stk n ((s - 16).toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
      ssink n maxP L0 live F 34 120 v aidx ta (A 578) w ∗ n ↦[wms][ aptr.toNat ] ab)
    iprop(stk n ((s - 16).toNat - 48) 48 ∗ n ↦[i32][ dp.toNat ] v ∗
      ssink n maxP L0 live F 34 120 v aidx ta (A 578) (w ++ ab) ∗ n ↦[wms][ aptr.toNat ] ab)
    (costS cfg F 120 alen.toNat) $$ [Hi H856 H923 H779 H840 Sw]
  · iframe Hi H856 H923 H779 H840 Sw
  iunfold K179
  iapply (MFunSpec_frame (Fr := iprop(stk n (s.toNat - 192) 128 ∗ Y)) ?_ ?_) $$ S179
  · intro args
    iintro ⟨%ha, Hg, HF, Hs, HS, Hd, ⟨HW, Hab⟩, HY⟩
    icases stkSp 128 64 rfl $$ Hs with ⟨Hs1, Hs⟩
    icases stkSp 48 16 rfl $$ Hs with ⟨Hs2, Hs3⟩
    iframe Hs1 HY Hg HF HW HS Hd Hab
    isplitr; · ipureintro; exact ha
    isplitl [Hs3]
    · iapply stkA (by omega) $$ Hs3
    iapply stkA (by omega) $$ Hs2
  · intro args rs
    iintro ⟨⟨Hs1, HY⟩, %hrs, Hg, Hs3, HW, HF, Hs2, Hd, HS, Hab⟩
    iframe Hg HF HS Hd HW Hab HY
    isplitr; · ipureintro; exact hrs
    iapply stkJ (a := s.toNat - 192) (b := s.toNat - 192 + 128) (k1 := 128) (k2 := 64) rfl rfl
    iframe Hs1
    iapply stkJ (a := s.toNat - 192 + 128) (b := s.toNat - 192 + 128 + 48) (k1 := 48) (k2 := 16) rfl rfl
    isplitl [Hs2]
    · iapply stkA (by omega) $$ Hs2
    iapply stkA (by omega) $$ Hs3

end Spec

end WNear.Binary.DepositLog
