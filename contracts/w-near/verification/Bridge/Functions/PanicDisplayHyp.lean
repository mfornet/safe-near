import Bridge.Functions.PanicDisplayArgs

/-!
# The two `write!`s of `<PanicInfo as Display>` (885) as instances of 872's hypotheses

885 formats, after `"panicked at "`:

* the message: `write!(f, "'{}', ", x)`, `Arguments { pieces: [("'", 1), ("', ", 3)] at 1070688,
  args: [(&x, fi)] at sp + 16 }`, `x` at `sp + 12`; for `begin_panic`'s payload `x` is the address of
  the `&str` and `fi` is 201 (886): `hypA_pay`, an instance of `FmtWriteT.Hyp872T` (the trailing piece);
* the location: `write!(f, "{}:{}:{}", file, line, col)`, `Arguments { pieces: [("", 0), (":", 1),
  (":", 1)] at 1070708, args: [(loc, 195), (loc + 8, 3), (loc + 12, 3)] at sp + 16 }`: `hypB_loc`, an
  instance of `FmtWriteN.Hyp872` (three pieces, three arguments: 880 and twice 870).

Both on the sink `SinkW`: the states `StA`/`StB` are the writer `W` after the bytes written so far
(`partA`/`partB`), the stack the writes use below 872's frame (112 bytes; 160 for the location, whose
`fmt_u64` has a frame of 48) and what they read (`XA`/`XB`): the pieces' bytes, the payload's `&str`
and bytes, the `Location`'s words, the file's bytes and the digit table.
-/

namespace WNear.Binary.PanicDisplay

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtPad (fmtr)
open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.FmtWriteN (fmtrP Hyp872)
open WNear.Binary.FmtWriteT (Hyp872T)
open WNear.Binary.FmtStrPad (cost856)
open WNear.Binary.FmtU64 (sinkSpec64 f870_small cost870 cost936)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

/-- `"'"`. -/
def qp : List UInt8 := [39]
/-- `"', "`. -/
def qcp : List UInt8 := [39, 44, 32]
/-- `":"`. -/
def colon : List UInt8 := [58]

theorem qp_eq : qp = "'".toUTF8.toList := by decide +kernel
theorem qcp_eq : qcp = "', ".toUTF8.toList := by decide +kernel
theorem colon_eq : colon = ":".toUTF8.toList := by decide +kernel

/-- The message part after the `i`-th write. -/
def partA (msg : List UInt8) : Nat → List UInt8
  | 0 => []
  | 1 => qp
  | 2 => qp ++ msg
  | _ => qp ++ msg ++ qcp

/-- The location part after the `i`-th write. -/
def partB (file dl dc : List UInt8) : Nat → List UInt8
  | 0 => []
  | 1 => []
  | 2 => file
  | 3 => file ++ colon
  | 4 => file ++ colon ++ dl
  | 5 => file ++ colon ++ dl ++ colon
  | _ => file ++ colon ++ dl ++ colon ++ dc

def pptrA (j : Nat) : UInt32 := if j = 0 then 1070684 else 1070685
def plenA (j : Nat) : UInt32 := if j = 0 then 1 else 3
def pptrB (j : Nat) : UInt32 := if j = 0 then 1067136 else 1070704
def plenB (j : Nat) : UInt32 := if j = 0 then 0 else 1
def vpB (loc : UInt32) (j : Nat) : UInt32 := if j = 0 then loc else if j = 1 then loc + 8 else loc + 12
def fiB (j : Nat) : UInt32 := if j = 0 then 195 else 3
def bB (A : Nat → Nat) (j : Nat) : Nat := if j = 0 then A 880 else A 870
noncomputable def codeBB (j : Nat) : Func := if j = 0 then f880 else f870

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A write on the sink at `sp`, with `N ≥ 112` bytes of stack and the bytes `sb` at `p` taken from
`X` (`hX`), in the shape of 872's hypotheses. -/
theorem sinkW_piece (cfg : WasmConfig) (lim : ExecLimits) (D d inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat)
    (sp p k : UInt32) (N : Nat) (w w' sb : List UInt8) (X : IProp GF) (hdD : d ≤ D) (hN : 112 ≤ N)
    (hspN : N ≤ sp.toNat) (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hwB : w.length + k.toNat ≤ B) (hw' : w' = w ++ sb)
    (hX : X ⊢ n ↦[wms][ p.toNat ] sb ∗ (n ↦[wms][ p.toNat ] sb -∗ X)) :
    SinkW cfg lim D inst mi n g gt data code W B Kw Cg ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi code Cg
        (fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (stk n (sp.toNat - N) N ∗ W w ∗ X)))
        (fun _ => Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (stk n (sp.toNat - N) N ∗ W w' ∗ X))) := by
  subst hw'
  iintro #Sw
  iunfold SinkW at Sw
  ihave #S := Sw $$ %d %sp %p %k %w %sb %⟨hdD, by omega, hsb, hp, hwB⟩
  iapply (MFunSpec_frame (GF := GF) (Fr := iprop(stk n (sp.toNat - N) (N - 112) ∗
      (n ↦[wms][ p.toNat ] sb -∗ X)))
    (P := fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        stk n (sp.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        stk n (sp.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb))
    (fun args => by
      iintro ⟨%ha, Hg, Hs, HW, HX⟩
      icases hX $$ HX with ⟨Hp, HX⟩
      icases stkSp (N - 112) 112 (by omega) $$ Hs with ⟨Hs1, Hs2⟩
      iframe Hs1 HX Hg HW Hp
      isplitr
      · ipureintro; exact ha
      iapply stkA (by omega) $$ Hs2)
    (fun args rs => by
      iintro ⟨⟨Hs1, HX⟩, %hrs, Hg, Hs2, HW, Hp⟩
      iframe Hg HW
      isplitr
      · ipureintro; exact hrs
      isplitl [Hs1 Hs2]
      · iapply stkJ (a := sp.toNat - N) (b := sp.toNat - 112) (k1 := N - 112) (k2 := 112) (by omega) (by omega)
        iframe Hs1 Hs2
      iapply HX $$ Hp))
  iexact S

/-! ## The message: the payload's `&str` (`begin_panic`) -/

/-- What the message's writes read: the pieces' bytes; the payload's `&str` `(m, l)` at `pp`, its
address at `y`, its bytes. -/
def XA (n : Nat) (y pp m l : UInt32) (msg : List UInt8) : IProp GF :=
  iprop((n ↦[wms][ 1070684 ] qp ∗ n ↦[wms][ 1070685 ] qcp) ∗
    (n ↦[i32][ y.toNat ] pp ∗ n ↦[i32][ pp.toNat ] m ∗ n ↦[i32][ pp.toNat + 4 ] l ∗ n ↦[wms][ m.toNat ] msg))

/-- The state of the message's writes, below 872's frame `s - 48`. -/
def StA (n : Nat) (s : UInt32) (W : List UInt8 → IProp GF) (w1 : List UInt8) (y pp m l : UInt32)
    (msg : List UInt8) (i : Nat) : IProp GF :=
  iprop(stk n ((s - 48).toNat - 112) 112 ∗ W (w1 ++ partA msg i) ∗ XA n y pp m l msg)

/-- The message's arrays: the pieces at 1070688, the argument `(y, 201)` at `argp`, the table entry. -/
def MA (n ta : Nat) (A : Nat → Nat) (argp y : UInt32) : IProp GF :=
  iprop((n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 ] pptrA 0 ∗
      n ↦[i32][ (1070688 : UInt32).toNat + 8 * 0 + 4 ] plenA 0) ∗
    (n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 ] pptrA 1 ∗
      n ↦[i32][ (1070688 : UInt32).toNat + 8 * 1 + 4 ] plenA 1) ∗
    (n ↦[i32][ argp.toNat + 8 * 0 ] y ∗ n ↦[i32][ argp.toNat + 8 * 0 + 4 ] 201 ∗
      ta ↦[wt][ (201 : UInt32).toNat ] Ref.func (A 886)))

/-- The code the message's writes run (persistent). -/
def CA (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗
    A 886 ↪[wf] FuncInst.wasm types[13]! inst f886 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
    SinkW cfg lim D inst mi n g gt data code W B Kw Cg)

instance (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    Persistent (CA cfg lim D inst mi A n g gt data a code W B Kw Cg) := by
  unfold CA; infer_instance

/-- The cost of the message's argument (886). -/
noncomputable def KBA (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  activationGas cfg.regularOpCost (entryLocals f886 [.i32 0, .i32 0]) + cost880 cfg code Kw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`Hyp872T` for the payload's message**: `"'"`, the `&str` through 886, `"', "`. -/
theorem hypA_pay (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 4 ≤ D) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s data vtab idx argp y pp m l : UInt32) (a : Nat) (code : Func)
    (W : List UInt8 → IProp GF) (B Kw : Nat) (w1 msg : List UInt8) (hs : 160 ≤ s.toNat)
    (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hmsg : msg.length = l.toNat) (hml : m.toNat + l.toNat ≤ 2 ^ 32)
    (hwB : w1.length + 4 + msg.length ≤ B) :
    Hyp872T (GF := GF) cfg lim d inst mi n g ta Cg gt s data vtab idx 1070688 argp 1 pptrA plenA
      (fun _ => y) (fun _ => 201) (fun _ => A 886) (fun _ => f886) a code
      (CA cfg lim D inst mi A n g gt data a code W B Kw Cg) (MA n ta A argp y)
      (StA n s W w1 y pp m l msg) Kw (cost880 cfg code Kw) (KBA cfg code Kw) := by
  have hlt := s.toNat_lt
  have hs48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hf8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, hs48]; omega
  have hj2 : ∀ j, j < (1 : UInt32).toNat + 1 → j = 0 ∨ j = 1 := fun j hj => by
    have : (1 : UInt32).toNat = 1 := rfl
    omega
  have hj1 : ∀ j, j < (1 : UInt32).toNat → j = 0 := fun j hj => by
    have : (1 : UInt32).toNat = 1 := rfl
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the pieces array
    intro j hj
    rcases hj2 j hj with rfl | rfl
    · iintro H
      iunfold MA at H
      icases H with ⟨⟨P0, P4⟩, Q, R⟩
      iframe P0 P4
      iintro ⟨P0, P4⟩
      iunfold MA
      iframe P0 P4 Q R
    · iintro H
      iunfold MA at H
      icases H with ⟨P, ⟨Q0, Q4⟩, R⟩
      iframe Q0 Q4
      iintro ⟨Q0, Q4⟩
      iunfold MA
      iframe P Q0 Q4 R
  · -- the arguments array
    intro j hj
    rcases hj1 j hj
    iintro H
    iunfold MA at H
    icases H with ⟨P, Q, ⟨R0, R4, Rt⟩⟩
    iframe R0 R4 Rt
    iintro ⟨R0, R4, Rt⟩
    iunfold MA
    iframe P Q R0 R4 Rt
  · iintro #C
    iunfold CA at C
    icases C with ⟨#Hi, -, -, #Ha, -⟩
    iframe Hi Ha
  · -- the pieces' writes
    intro j hj
    rcases hj2 j hj with rfl | rfl
    · simp only [pptrA, plenA, StA, Nat.reduceMul, ↓reduceIte]
      iintro #C
      iunfold CA at C
      icases C with ⟨-, -, -, -, #Sw⟩
      iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1070684 1 112
        (w1 ++ partA msg 0) (w1 ++ partA msg 1) qp (XA n y pp m l msg) (by omega) le_rfl (by omega)
        rfl (by decide) (by simp [partA]; omega) (by simp [partA])
        (by
          iintro H
          iunfold XA at H
          icases H with ⟨⟨P0, P1⟩, Q⟩
          isplitl [P0]
          · iapply memBytes_addr _ $$ P0; rfl
          iintro P0
          iunfold XA
          iframe P1 Q
          iapply memBytes_addr _ $$ P0; rfl)
      iexact Sw
    · simp only [pptrA, plenA, StA, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff]
      iintro #C
      iunfold CA at C
      icases C with ⟨-, -, -, -, #Sw⟩
      iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1070685 3 112
        (w1 ++ partA msg 2) (w1 ++ partA msg 3) qcp (XA n y pp m l msg) (by omega) le_rfl (by omega)
        rfl (by decide) (by simp [partA, qp]; omega) (by simp [partA])
        (by
          iintro H
          iunfold XA at H
          icases H with ⟨⟨P0, P1⟩, Q⟩
          isplitl [P1]
          · iapply memBytes_addr _ $$ P1; rfl
          iintro P1
          iunfold XA
          iframe P0 Q
          iapply memBytes_addr _ $$ P1; rfl)
      iexact Sw
  · intro j hj
    rcases hj1 j hj
    iintro #C
    iunfold CA at C
    icases C with ⟨-, -, #H886, -, -⟩
    iexact H886
  · -- the argument: the `&str` through 886
    intro j hj
    rcases hj1 j hj
    simp only [StA, Nat.reduceMul, Nat.reduceAdd]
    iintro #C
    iunfold CA at C
    icases C with ⟨#Hi, #H856, -, #Ha, #Sw⟩
    ihave #S := f886_w cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 48)
      (s - 48 + 8) data vtab idx y pp m l (by omega) (by omega) a code W B Kw (w1 ++ partA msg 1) msg hmsg hml
      (by simp [partA, qp]; omega) $$ [Hi H856 Ha Sw]
    · iframe Hi H856 Ha Sw
    iapply (MFunSpec_frame (GF := GF) (Fr := iprop(n ↦[wms][ 1070684 ] qp ∗ n ↦[wms][ 1070685 ] qcp))
      (fun args => by
        iintro ⟨%ha, Hg, HF, Hs, HW, HX⟩
        iunfold XA at HX
        icases HX with ⟨P, Y0, P0, P4, Hm⟩
        iframe P
        iframe HF Y0 P0 P4 Hg Hs HW Hm
        ipureintro; exact ha)
      (fun args rs => by
        iintro ⟨P, %hrs, HF, Y0, P0, P4, Hg, Hs, HW, Hm⟩
        iframe Hg HF Hs
        isplitr
        · ipureintro; exact hrs
        isplitl [HW]
        · simp only [partA, List.append_assoc]; iexact HW
        iunfold XA
        iframe P Y0 P0 P4 Hm)) $$ S
  · intro j hj
    rcases hj1 j hj
    unfold KBA; omega

/-! ## The location -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- 880 in the shape of 872's hypotheses: `N ≥ 112` bytes of stack, the `&str` and its bytes taken
from `X`. -/
theorem arg880 (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 2 ≤ D) (hd : d + 2 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp f data vtab idx x p k : UInt32) (hf : f.toNat + 32 ≤ 2 ^ 32) (N : Nat)
    (hN : 112 ≤ N) (hsp : N ≤ sp.toNat) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat)
    (w w' sb : List UInt8) (hsb : sb.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hwB : w.length + k.toNat ≤ B) (hw' : w' = w ++ sb) (X : IProp GF)
    (hX : X ⊢ n ↦[i32][ x.toNat ] p ∗ n ↦[i32][ x.toNat + 4 ] k ∗ n ↦[wms][ p.toNat ] sb ∗
      (n ↦[i32][ x.toNat ] p -∗ n ↦[i32][ x.toNat + 4 ] k -∗ n ↦[wms][ p.toNat ] sb -∗ X)) :
    inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW cfg lim D inst mi n g gt data code W B Kw Cg ⊢
      MFunSpec (GF := GF) cfg lim d types[13]! inst mi f880 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          fmtrP n ta f data vtab idx a ∗ (stk n (sp.toNat - N) N ∗ W w ∗ X)))
        (fun _ => cost880 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          fmtrP n ta f data vtab idx a ∗ (stk n (sp.toNat - N) N ∗ W w' ∗ X))) := by
  subst hw'
  iintro ⟨#Hi, #H856, #Ha, #Sw⟩
  ihave #S := f880_w cfg lim d types[13]! rfl inst mi A n g ta hm D hdD hd Cg gt sp f data vtab idx x p k hf
    (by omega) a code W B Kw w sb hsb hp hwB $$ [Hi H856 Ha Sw]
  · iframe Hi H856 Ha Sw
  iapply (MFunSpec_frame (GF := GF) (Fr := iprop(stk n (sp.toNat - N) (N - 112) ∗
      (n ↦[i32][ x.toNat ] p -∗ n ↦[i32][ x.toNat + 4 ] k -∗ n ↦[wms][ p.toNat ] sb -∗ X)))
    (fun args => by
      iintro ⟨%ha, Hg, HF, Hs, HW, HX⟩
      icases hX $$ HX with ⟨X0, X4, Hp, HX⟩
      icases stkSp (N - 112) 112 (by omega) $$ Hs with ⟨Hs1, Hs2⟩
      iframe Hs1 HX HF X0 X4 Hg HW Hp
      isplitr
      · ipureintro; exact ha
      iapply stkA (by omega) $$ Hs2)
    (fun args rs => by
      iintro ⟨⟨Hs1, HX⟩, %hrs, HF, X0, X4, Hg, Hs2, HW, Hp⟩
      iframe Hg HF HW
      isplitr
      · ipureintro; exact hrs
      isplitl [Hs1 Hs2]
      · iapply stkJ (a := sp.toNat - N) (b := sp.toNat - 112) (k1 := N - 112) (k2 := 112) (by omega) (by omega)
        iframe Hs1 Hs2
      iapply HX $$ X0 X4 Hp)) $$ S

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- 870 in the shape of 872's hypotheses: 160 bytes of stack (936's frame, then the sink's), the
`u32` and the digit table taken from `X`. -/
theorem arg870 (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 3 ≤ D) (hd : d + 4 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp f data vtab idx x u : UInt32) (hu : u.toNat < 10000)
    (hf : f.toNat + 32 ≤ 2 ^ 32) (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (hsp : 160 ≤ sp.toNat)
    (hsp2 : sp.toNat ≤ 2 ^ 32 - 16) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw : Nat)
    (w w' : List UInt8) (hwB : w.length + (decDigits u.toNat).length ≤ B) (hw' : w' = w ++ decDigits u.toNat)
    (X : IProp GF)
    (hX : X ⊢ n ↦[i32][ x.toNat ] u ∗ n ↦[wms][ 1070974 ] lut ∗
      (n ↦[i32][ x.toNat ] u -∗ n ↦[wms][ 1070974 ] lut -∗ X)) :
    A 936 ↪[wf] FuncInst.wasm types[68]! inst f936 ∗
      A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗ A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗
      inst ↪[inst] mi ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
      SinkW cfg lim D inst mi n g gt data code W B Kw Cg ⊢
      MFunSpec (GF := GF) cfg lim d types[13]! inst mi f870 Cg
        (fun args => iprop(⌜args = [.i32 x, .i32 f]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          fmtrP n ta f data vtab idx a ∗ (stk n (sp.toNat - 160) 160 ∗ W w ∗ X)))
        (fun _ => cost870 cfg code Kw)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          fmtrP n ta f data vtab idx a ∗ (stk n (sp.toNat - 160) 160 ∗ W w' ∗ X))) := by
  subst hw'
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hL := FmtDigits.decDigits_length_le 5 u.toNat (by omega) (by simp; omega)
  iintro ⟨#H936, #H903, #H910, #Hi, #Ha, #Sw⟩
  ihave #S64 := sinkW_64 cfg lim D (d + 3) inst mi n g gt (sp - 48) data code W B Kw Cg w
    (decDigits u.toNat) hdD (by omega) (by omega) (by omega) hwB $$ Sw
  ihave #S := f870_small cfg lim d types[13]! rfl inst mi A n g ta hm hd Cg gt sp x f data vtab idx u hu
    (by omega) hf hvt a code iprop(stk n ((sp - 48).toNat - 112) 112 ∗ W w)
    iprop(stk n ((sp - 48).toNat - 112) 112 ∗ W (w ++ decDigits u.toNat)) Kw $$ [H936 H903 H910 Hi Ha S64]
  · iframe H936 H903 H910 Hi Ha S64
  iapply (MFunSpec_frame (GF := GF) (Fr := iprop(n ↦[i32][ (f.toNat) + 16 ] 0 ∗
      (n ↦[i32][ x.toNat ] u -∗ n ↦[wms][ 1070974 ] lut -∗ X)))
    (fun args => by
      iintro ⟨%ha, Hg, HF, Hs, HW, HX⟩
      icases hX $$ HX with ⟨Xu, Hl, HX⟩
      iunfold fmtrP at HF
      icases HF with ⟨HF, F16⟩
      icases stkSp 112 48 (by omega) $$ Hs with ⟨Hs1, Hs2⟩
      iframe F16 HX Hg HF Xu Hl HW
      isplitr
      · ipureintro; exact ha
      isplitl [Hs2]
      · iapply stkA (by omega) $$ Hs2
      iapply stkA (by omega) $$ Hs1)
    (fun args rs => by
      iintro ⟨⟨F16, HX⟩, %hrs, Hg, Hs2, Xu, HF, Hl, Hs1, HW⟩
      iframe Hg HW
      isplitr
      · ipureintro; exact hrs
      isplitl [HF F16]
      · iunfold fmtrP; iframe HF F16
      isplitl [Hs1 Hs2]
      · iapply stkJ (a := sp.toNat - 160) (b := sp.toNat - 48) (k1 := 112) (k2 := 48) (by omega) (by omega)
        isplitl [Hs1]
        · iapply stkA (by omega) $$ Hs1
        iexact Hs2
      iapply HX $$ Xu Hl)) $$ S

/-- What the location's writes read: `":"`, the digit table, the `Location`'s words, the file's bytes. -/
def XB (n : Nat) (loc file flen line col : UInt32) (fileB : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ 1070704 ] colon ∗ n ↦[wms][ 1070974 ] lut ∗
    (n ↦[i32][ loc.toNat ] file ∗ n ↦[i32][ loc.toNat + 4 ] flen ∗ n ↦[i32][ loc.toNat + 8 ] line ∗
      n ↦[i32][ loc.toNat + 12 ] col) ∗ n ↦[wms][ file.toNat ] fileB)

/-- The state of the location's writes, below 872's frame `s - 48`. -/
def StB (n : Nat) (s : UInt32) (W : List UInt8 → IProp GF) (w2 : List UInt8) (loc file flen line col : UInt32)
    (fileB : List UInt8) (i : Nat) : IProp GF :=
  iprop(stk n ((s - 48).toNat - 160) 160 ∗
    W (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) i) ∗ XB n loc file flen line col fileB)

/-- The location's arrays: the pieces at 1070708, the arguments at `argp`, the table entries 195 and 3. -/
def MB (n ta : Nat) (A : Nat → Nat) (argp loc : UInt32) : IProp GF :=
  iprop((n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 ] pptrB 0 ∗
      n ↦[i32][ (1070708 : UInt32).toNat + 8 * 0 + 4 ] plenB 0) ∗
    (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 ] pptrB 1 ∗
      n ↦[i32][ (1070708 : UInt32).toNat + 8 * 1 + 4 ] plenB 1) ∗
    (n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 ] pptrB 2 ∗
      n ↦[i32][ (1070708 : UInt32).toNat + 8 * 2 + 4 ] plenB 2) ∗
    (n ↦[i32][ argp.toNat + 8 * 0 ] vpB loc 0 ∗ n ↦[i32][ argp.toNat + 8 * 0 + 4 ] fiB 0) ∗
    (n ↦[i32][ argp.toNat + 8 * 1 ] vpB loc 1 ∗ n ↦[i32][ argp.toNat + 8 * 1 + 4 ] fiB 1) ∗
    (n ↦[i32][ argp.toNat + 8 * 2 ] vpB loc 2 ∗ n ↦[i32][ argp.toNat + 8 * 2 + 4 ] fiB 2) ∗
    ta ↦[wt][ (195 : UInt32).toNat ] Ref.func (A 880) ∗ ta ↦[wt][ (3 : UInt32).toNat ] Ref.func (A 870))

/-- The code the location's writes run (persistent). -/
def CB (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    IProp GF :=
  iprop(inst ↪[inst] mi ∗ A 856 ↪[wf] FuncInst.wasm types[15]! inst f856 ∗
    A 880 ↪[wf] FuncInst.wasm types[13]! inst f880 ∗ A 870 ↪[wf] FuncInst.wasm types[13]! inst f870 ∗
    A 936 ↪[wf] FuncInst.wasm types[68]! inst f936 ∗ A 903 ↪[wf] FuncInst.wasm types[67]! inst f903 ∗
    A 910 ↪[wf] FuncInst.wasm types[33]! inst f910 ∗ a ↪[wf] FuncInst.wasm types[15]! inst code ∗
    SinkW cfg lim D inst mi n g gt data code W B Kw Cg)

instance (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (a : Nat) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    Persistent (CB cfg lim D inst mi A n g gt data a code W B Kw Cg) := by
  unfold CB; infer_instance

/-- The location's arguments' cost, uniformly. -/
noncomputable def KbB (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  cost880 cfg code Kw + cost870 cfg code Kw

noncomputable def KBB (cfg : WasmConfig) (code : Func) (Kw : Nat) : Nat :=
  activationGas cfg.regularOpCost (entryLocals f880 [.i32 0, .i32 0]) +
    activationGas cfg.regularOpCost (entryLocals f870 [.i32 0, .i32 0]) + KbB cfg code Kw

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **`Hyp872` for the location**: `""`, the file through 880, `":"`, the line through 870, `":"`, the
column through 870. -/
theorem hypB_loc (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (D : Nat) (hdD : d + 4 ≤ D) (hd : d + 5 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s data vtab idx argp loc file flen line col : UInt32) (a : Nat) (code : Func)
    (W : List UInt8 → IProp GF) (B Kw : Nat) (w2 fileB : List UInt8) (hs : 208 ≤ s.toNat)
    (hs2 : s.toNat ≤ 2 ^ 32 - 16) (hvt : vtab.toNat + 16 ≤ 2 ^ 32) (hloc : loc.toNat + 16 ≤ 2 ^ 32)
    (hfl : fileB.length = flen.toNat) (hfile : file.toNat + flen.toNat ≤ 2 ^ 32)
    (hline : line.toNat < 10000) (hcol : col.toNat < 10000)
    (hwB : w2.length + fileB.length + 2 + (decDigits line.toNat).length + (decDigits col.toNat).length ≤ B) :
    Hyp872 (GF := GF) cfg lim d inst mi n g ta Cg gt s data vtab idx 1070708 argp 3 pptrB plenB
      (vpB loc) fiB (bB A) codeBB a code
      (CB cfg lim D inst mi A n g gt data a code W B Kw Cg) (MB n ta A argp loc)
      (StB n s W w2 loc file flen line col fileB) Kw (KbB cfg code Kw) (KBB cfg code Kw) := by
  have hlt := s.toNat_lt
  have hs48 : (s - 48).toNat = s.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hf8 : (s - 48 + 8).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, hs48]; omega
  have h8 : (loc + 8).toNat = loc.toNat + 8 := by simp [UInt32.toNat_add]; omega
  have h12 : (loc + 12).toNat = loc.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hj3 : ∀ j, j < (3 : UInt32).toNat → j = 0 ∨ j = 1 ∨ j = 2 := fun j hj => by
    have : (3 : UInt32).toNat = 3 := rfl
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the pieces array
    intro j hj
    rcases hj3 j hj with rfl | rfl | rfl
    · iintro H
      iunfold MB at H
      icases H with ⟨⟨P0, P4⟩, Q, R, T⟩
      iframe P0 P4
      iintro ⟨P0, P4⟩
      iunfold MB
      iframe P0 P4 Q R T
    · iintro H
      iunfold MB at H
      icases H with ⟨P, ⟨Q0, Q4⟩, R, T⟩
      iframe Q0 Q4
      iintro ⟨Q0, Q4⟩
      iunfold MB
      iframe P Q0 Q4 R T
    · iintro H
      iunfold MB at H
      icases H with ⟨P, Q, ⟨R0, R4⟩, T⟩
      iframe R0 R4
      iintro ⟨R0, R4⟩
      iunfold MB
      iframe P Q R0 R4 T
  · -- the arguments array
    intro j hj
    rcases hj3 j hj with rfl | rfl | rfl
    · iintro H
      iunfold MB at H
      icases H with ⟨P, Q, R, ⟨T0, T4⟩, U, V, T195, T3⟩
      iframe T0 T4
      simp only [fiB, bB, ↓reduceIte]
      iframe T195
      iintro ⟨T0, T4, T195⟩
      iunfold MB
      simp only [fiB, ↓reduceIte, Nat.reduceEqDiff]
      iframe P Q R T0 T4 U V T195 T3
    · iintro H
      iunfold MB at H
      icases H with ⟨P, Q, R, T, ⟨U0, U4⟩, V, T195, T3⟩
      iframe U0 U4
      simp only [fiB, bB, ↓reduceIte, Nat.reduceEqDiff]
      iframe T3
      iintro ⟨U0, U4, T3⟩
      iunfold MB
      simp only [fiB, ↓reduceIte, Nat.reduceEqDiff]
      iframe P Q R T U0 U4 V T195 T3
    · iintro H
      iunfold MB at H
      icases H with ⟨P, Q, R, T, U, ⟨V0, V4⟩, T195, T3⟩
      iframe V0 V4
      simp only [fiB, bB, ↓reduceIte, Nat.reduceEqDiff]
      iframe T3
      iintro ⟨V0, V4, T3⟩
      iunfold MB
      simp only [fiB, ↓reduceIte, Nat.reduceEqDiff]
      iframe P Q R T U V0 V4 T195 T3
  · iintro #C
    iunfold CB at C
    icases C with ⟨#Hi, -, -, -, -, -, -, #Ha, -⟩
    iframe Hi Ha
  · -- the pieces' writes
    intro j hj
    rcases hj3 j hj with rfl | rfl | rfl
    · simp only [pptrB, plenB, StB, Nat.reduceMul, ↓reduceIte]
      iintro #C
      iunfold CB at C
      icases C with ⟨-, -, -, -, -, -, -, -, #Sw⟩
      iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1067136 0 160
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 0)
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 1) [] (XB n loc file flen line col fileB)
        (by omega) (by omega) (by omega) rfl (by decide) (by simp [partB]; omega) (by simp [partB])
        (by
          iintro H
          iframe H
          isplitr
          · iapply FmtString.memBytes_nil
          iintro -; iempintro)
      iexact Sw
    · simp only [pptrB, plenB, StB, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff]
      iintro #C
      iunfold CB at C
      icases C with ⟨-, -, -, -, -, -, -, -, #Sw⟩
      iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1070704 1 160
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 2)
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 3) colon (XB n loc file flen line col fileB)
        (by omega) (by omega) (by omega) rfl (by decide) (by simp [partB, colon]; omega) (by simp [partB])
        (by
          iintro H
          iunfold XB at H
          icases H with ⟨P0, Q⟩
          isplitl [P0]
          · iapply memBytes_addr _ $$ P0; rfl
          iintro P0
          iunfold XB
          iframe Q
          iapply memBytes_addr _ $$ P0; rfl)
      iexact Sw
    · simp only [pptrB, plenB, StB, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff]
      iintro #C
      iunfold CB at C
      icases C with ⟨-, -, -, -, -, -, -, -, #Sw⟩
      iapply sinkW_piece cfg lim D (d + 1) inst mi n g gt data code W B Kw Cg (s - 48) 1070704 1 160
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 4)
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 5) colon (XB n loc file flen line col fileB)
        (by omega) (by omega) (by omega) rfl (by decide) (by simp [partB, colon]; omega) (by simp [partB])
        (by
          iintro H
          iunfold XB at H
          icases H with ⟨P0, Q⟩
          isplitl [P0]
          · iapply memBytes_addr _ $$ P0; rfl
          iintro P0
          iunfold XB
          iframe Q
          iapply memBytes_addr _ $$ P0; rfl)
      iexact Sw
  · intro j hj
    rcases hj3 j hj with rfl | rfl | rfl
    · simp only [bB, codeBB, ↓reduceIte]
      iintro #C
      iunfold CB at C
      icases C with ⟨-, -, #H880, -, -, -, -, -, -⟩
      iexact H880
    · simp only [bB, codeBB, ↓reduceIte, Nat.reduceEqDiff]
      iintro #C
      iunfold CB at C
      icases C with ⟨-, -, -, #H870, -, -, -, -, -⟩
      iexact H870
    · simp only [bB, codeBB, ↓reduceIte, Nat.reduceEqDiff]
      iintro #C
      iunfold CB at C
      icases C with ⟨-, -, -, #H870, -, -, -, -, -⟩
      iexact H870
  · -- the arguments' formatters
    intro j hj
    rcases hj3 j hj with rfl | rfl | rfl
    · simp only [vpB, codeBB, StB, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte]
      iintro #C
      iunfold CB at C
      icases C with ⟨#Hi, #H856, -, -, -, -, -, #Ha, #Sw⟩
      ihave #S := arg880 cfg lim (d + 1) inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 48) (s - 48 + 8)
        data vtab idx loc file flen (by omega) 160 (by omega) (by omega) a code W B Kw
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 1)
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 2) fileB hfl hfile
        (by simp [partB]; omega) (by simp [partB]) (XB n loc file flen line col fileB)
        (by
          iintro H
          iunfold XB at H
          icases H with ⟨P0, Hl, ⟨L0, L4, L8, L12⟩, Hf⟩
          iframe L0 L4 Hf
          iintro L0 L4 Hf
          iunfold XB
          iframe P0 Hl L0 L4 L8 L12 Hf) $$ [Hi H856 Ha Sw]
      · iframe Hi H856 Ha Sw
      iapply (MFunSpec_cost (K' := fun _ => KbB cfg code Kw) (fun _ => by simp only [KbB]; omega)) $$ S
    · simp only [vpB, codeBB, StB, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff]
      iintro #C
      iunfold CB at C
      icases C with ⟨#Hi, -, -, -, #H936, #H903, #H910, #Ha, #Sw⟩
      ihave #S := arg870 cfg lim (d + 1) inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 48) (s - 48 + 8)
        data vtab idx (loc + 8) line hline (by omega) hvt (by omega) (by omega) a code W B Kw
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 3)
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 4)
        (by simp [partB, colon]; omega) (by simp [partB]) (XB n loc file flen line col fileB)
        (by
          iintro H
          iunfold XB at H
          icases H with ⟨P0, Hl, ⟨L0, L4, L8, L12⟩, Hf⟩
          rw [h8]
          iframe L8 Hl
          iintro L8 Hl
          iunfold XB
          iframe P0 Hl L0 L4 L8 L12 Hf) $$ [H936 H903 H910 Hi Ha Sw]
      · iframe H936 H903 H910 Hi Ha Sw
      iapply (MFunSpec_cost (K' := fun _ => KbB cfg code Kw) (fun _ => by simp only [KbB]; omega)) $$ S
    · simp only [vpB, codeBB, StB, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.reduceEqDiff]
      iintro #C
      iunfold CB at C
      icases C with ⟨#Hi, -, -, -, #H936, #H903, #H910, #Ha, #Sw⟩
      ihave #S := arg870 cfg lim (d + 1) inst mi A n g ta hm D (by omega) (by omega) Cg gt (s - 48) (s - 48 + 8)
        data vtab idx (loc + 12) col hcol (by omega) hvt (by omega) (by omega) a code W B Kw
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 5)
        (w2 ++ partB fileB (decDigits line.toNat) (decDigits col.toNat) 6)
        (by simp [partB, colon]; omega) (by simp [partB]) (XB n loc file flen line col fileB)
        (by
          iintro H
          iunfold XB at H
          icases H with ⟨P0, Hl, ⟨L0, L4, L8, L12⟩, Hf⟩
          rw [h12]
          iframe L12 Hl
          iintro L12 Hl
          iunfold XB
          iframe P0 Hl L0 L4 L8 L12 Hf) $$ [H936 H903 H910 Hi Ha Sw]
      · iframe H936 H903 H910 Hi Ha Sw
      iapply (MFunSpec_cost (K' := fun _ => KbB cfg code Kw) (fun _ => by simp only [KbB]; omega)) $$ S
  · intro j hj
    rcases hj3 j hj with rfl | rfl | rfl <;> (unfold KBB; simp [codeBB]) <;> omega

end Spec

end WNear.Binary.PanicDisplay
