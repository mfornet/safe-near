import Bridge.Functions.ParseEscapeSurrogateSuccess
import Bridge.Functions.StrCost

/-!
# A successful escape's instruction budget is linear in the bytes consumed

The byte append is accounted separately by the scratch-growth contract. The
remaining Wasm work costs at most 200 regular operations per encoded byte,
including the leading backslash, without any error-construction reserve.
-/

namespace WNear.Binary.ParseEscapeSuccessCost

open Wasm Wasm.Near
open WNear.Binary.ParseEscape (escDecode escK hex4_some ue_hi ue_suffix)
open NearInterface.Json (hex4 unicodeEscape)

/-- The instruction allowance for the three successful escape paths. -/
def successOps : List UInt8 → Nat
  | 0x75 :: rest =>
    match hex4 rest with
    | some (nv, _) => if nv / 1024 = 54 then 2000 else 900
    | none => 900
  | _ => 400

/-- No Unicode prefix: the simple-escape allowance. -/
theorem successOps_nu (l : List UInt8) (h : ∀ rest, l ≠ 0x75 :: rest) : successOps l = 400 := by
  cases l with
  | nil => rfl
  | cons b rest =>
    by_cases hb : b = 0x75
    · subst hb; exact False.elim (h rest rfl)
    · simp [successOps, hb]

/-- A Unicode prefix without a high surrogate uses the BMP allowance. -/
theorem successOps_u0 (l rest : List UInt8) (hl : l = 0x75 :: rest)
    (h : ∀ nv r, hex4 rest = some (nv, r) → nv / 1024 ≠ 54) : successOps l = 900 := by
  subst l
  cases hh : hex4 rest with
  | none => simp [successOps, hh]
  | some p =>
    obtain ⟨nv, r⟩ := p
    simp [successOps, hh, h nv r hh]

/-- A high surrogate uses the pair allowance. -/
theorem successOps_u1 (l rest r : List UInt8) (nv : Nat) (hl : l = 0x75 :: rest)
    (hh : hex4 rest = some (nv, r)) (h : nv / 1024 = 54) : successOps l = 2000 := by
  simp [hl, successOps, hh, h]

/-- On success, all instruction work fits a fixed allowance per consumed encoded byte. -/
theorem successOps_le (l out : List UInt8) (m : Nat) (he : escDecode l = some (out, m)) :
    successOps l ≤ 200 * (m + 1) := by
  cases l with
  | nil => simp [escDecode] at he
  | cons b rest =>
    by_cases hb : b = 0x75
    · subst hb
      have he' := he
      change (unicodeEscape rest).map (fun p => (String.utf8EncodeChar p.1, 1 + (rest.length - p.2.length))) =
        some (out, m) at he'
      obtain ⟨⟨c, r⟩, hue, hp⟩ := Option.map_eq_some_iff.mp he'
      have hm : m = 1 + (rest.length - r.length) := (congrArg Prod.snd hp).symm
      have hlen := (ue_suffix rest r c hue).1
      cases hh : hex4 rest with
      | none => simp [unicodeEscape, hh] at hue
      | some p =>
        obtain ⟨nv, r1⟩ := p
        by_cases hhi : nv / 1024 = 54
        · have hnv : 0xD800 ≤ nv ∧ nv < 0xDC00 := by omega
          obtain ⟨r2, mv, r3, hshape, hh2, hmv⟩ :=
            ParseEscapeSurrogateSuccess.valid_high_tail rest r1 nv hh hnv (by simp [hue])
          have hfirst := hex4_some rest r1 nv hh
          have hsecond := hex4_some r2 r3 mv hh2
          have hue' := ue_hi rest r1 r2 nv hh hnv hshape
          rw [hue', hh2] at hue
          simp only [Option.bind_some, if_pos hmv, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hue
          have hr : r3 = r := hue.2
          have hshapeLen := congrArg List.length hshape
          have hfirstLen := congrArg List.length hfirst.2
          have hsecondLen := congrArg List.length hsecond.2
          simp only [List.length_cons, List.length_drop] at hshapeLen hfirstLen hsecondLen
          have hmlen : 11 ≤ m := by
            rw [hr] at hsecondLen
            omega
          simp [successOps, hh, hhi]
          omega
        · simp [successOps, hh, hhi]
          omega
    · rw [successOps_nu (b :: rest) (by intro r h; cases h; exact hb rfl)]
      have hlen := ParseStr.escDecode_len (b :: rest) out m he
      omega

/-- The success cost excludes all whole-input position scans. -/
def cost649 (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l : List UInt8) : Nat :=
  successOps l * cfg.regularOpCost +
    ScratchGrow.costExt cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat (escK l))

theorem cost649_le (cfg : WasmConfig) (F : Nat) (cap : UInt32) (acc l out : List UInt8) (m : Nat)
    (he : escDecode l = some (out, m)) :
    cost649 cfg F cap acc l ≤ 200 * (m + 1) * cfg.regularOpCost +
      ScratchGrow.costExt cfg F cap (UInt32.ofNat acc.length) (UInt32.ofNat out.length) := by
  unfold cost649
  simp only [escK, he]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right cfg.regularOpCost (successOps_le l out m he)) _

open WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.ParseEscape (escCode res649)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeEsc (hexTable)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.ScratchGrow (sbuf roomRes)

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Every successful escape has its actual scratch result at a cost without error reserves. -/
theorem f649_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s de ptr sc ptrS capS idx : UInt32) (bs acc : List UInt8) (j : Nat) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat)
    (hde : de.toNat + 12 ≤ 2 ^ 32) (hj : j ≤ bs.length) (hsc : sc.toNat + 12 ≤ 2 ^ 32)
    (hlen : bs.length + 16 < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hs : 144 ≤ s.toNat)
    (hcap : capS.toNat < 2 ^ 27) (hacc : acc.length + 4 < 2 ^ 27)
    (hvalid : (escDecode (bs.drop j)).isSome = true)
    (hr : roomRes hl maxP capS (UInt32.ofNat acc.length) (UInt32.ofNat (escK (bs.drop j)))) :
    escCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f649 Cg
        (fun args => iprop(⌜args = [.i32 de, .i32 sc]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗ rd n de ptr bs j ∗
          n ↦[i32][ sc.toNat ] ptrS ∗ n ↦[i32][ sc.toNat + 4 ] capS ∗
          n ↦[i32][ sc.toNat + 8 ] UInt32.ofNat acc.length ∗ sbuf n maxP hl live F ptrS capS acc ∗
          n ↦[wms][ 1062712 ] hexTable))
        (fun _ => cost649 cfg F capS acc (bs.drop j))
        (fun _ rs => iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 144) 144 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ 1062712 ] hexTable ∗ res649 n maxP hl live F de ptr bs j sc ptrS capS acc rs)) := by
  by_cases hu : ∃ rest, bs.drop j = 0x75 :: rest
  · obtain ⟨rest, hrest⟩ := hu
    have htail : bs.drop (j + 1) = rest := by
      have h := congrArg (List.drop 1) hrest
      simpa [List.drop_drop, Nat.add_comm] using h
    by_cases hh : ∃ nv r, hex4 (bs.drop (j + 1)) = some (nv, r) ∧ nv / 1024 = 54
    · obtain ⟨nv, r, hhex, hhi⟩ := hh
      have hops := successOps_u1 (bs.drop j) rest r nv hrest (by rw [← htail]; exact hhex) hhi
      simpa only [cost649, hops] using
        ParseEscapeSurrogateSuccess.f649_u1_success (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg
          gt s de ptr sc ptrS capS idx bs acc j maxP hl live F hde hj hsc hlen hptr hs hcap hacc
          hvalid ⟨rest, hrest⟩ ⟨nv, r, hhex, hhi⟩ hr
    · have hops := successOps_u0 (bs.drop j) rest hrest (fun nv r hhex hhi =>
        hh ⟨nv, r, by rw [htail]; exact hhex, hhi⟩)
      simpa only [cost649, hops] using
        ParseEscapeSuccess.f649_u0_success (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg
          gt s de ptr sc ptrS capS idx bs acc j maxP hl live F hde hj hsc hlen hptr hs hcap hacc
          hvalid ⟨rest, hrest⟩ (fun nv r hhex hhi => hh ⟨nv, r, hhex, hhi⟩) hr
  · have hops := successOps_nu (bs.drop j) (fun rest h => hu ⟨rest, h⟩)
    simpa only [cost649, hops] using
      ParseEscapeSuccess.f649_nu_success (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg
        gt s de ptr sc ptrS capS idx bs acc j maxP hl live F hde hj hsc hlen hptr hs hcap hacc
        hvalid (fun rest h => hu ⟨rest, h⟩) hr

end Proof

end WNear.Binary.ParseEscapeSuccessCost
