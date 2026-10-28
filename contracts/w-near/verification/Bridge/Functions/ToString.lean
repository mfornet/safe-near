import Bridge.Functions.FmtString
import Bridge.Functions.SerdeLeaves
import Bridge.Functions.VecDeref
import Binary.Code.Part07
import Bridge.Functions.SerializeStr

/-!
# `<U128 as Serialize>::serialize` (385) (M5)

`serialize(&self, ser)` is `ser.serialize_str(&self.0.to_string())`:

```
385  sp -= 64; String::new() at sp + 16 (1, 0, 0); *(sp + 28) = v (the &u128 cell)
     Argument::new(sp + 8, sp + 28, 92) (472); Arguments { pieces: (1051836, 1), fmt: None,
     args: (sp + 56, 1) } at sp + 32, the argument copied to sp + 56
     write_fmt(sp + 16, sp + 32) (746); expect (365); deref(sp, sp + 16) (779)
     r = serialize_str(ser, *sp, *(sp + 4)) (383); drop the String (321); sp += 64; r
```

`f385_gen` is parametric in `serialize_str`'s specification (`S383`, for any buffer `q` of the
`String`), which writes the digits to the serializer's output.
-/

namespace WNear.Binary.ToString

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.FmtDigits (decDigits lut)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDisplay (fmtCode)
open WNear.Binary.FmtSink (sinkCode strGrown grown)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_intro stk_addr roomFor)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.FmtWrite (argsAt pieceArg)
open WNear.Binary.FmtString (kOf fIn fOut cost746 f746_u128)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code 385 runs (persistent). -/
def tsCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(fmtCode inst mi A (A 759) f759 ∗ A 901 ↪[wf] FuncInst.wasm types[13]! inst f901 ∗
    A 353 ↪[wf] FuncInst.wasm types[13]! inst f353 ∗ A 872 ↪[wf] FuncInst.wasm types[15]! inst f872 ∗
    sinkCode n maxP inst mi A ∗ dropCode inst mi A ∗ A 746 ↪[wf] FuncInst.wasm types[13]! inst f746 ∗
    A 472 ↪[wf] FuncInst.wasm types[31]! inst f472 ∗ A 365 ↪[wf] FuncInst.wasm types[0]! inst f365 ∗
    A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 383 ↪[wf] FuncInst.wasm types[15]! inst f383 ∗
    A 321 ↪[wf] FuncInst.wasm types[0]! inst f321)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (tsCode (GF := GF) n maxP inst mi A) := by
  unfold tsCode; infer_instance

/-- The data `to_string` reads (owned, returned): the piece `""` at 1051836, the `String`
vtable's `write_str` slot (157) and the table entries 157 (`write_str`, 759) and 92 (353). -/
def tsData (n ta : Nat) (ptr0 : UInt32) (a759 a353 : Nat) : IProp GF :=
  iprop(n ↦[i32][ (1051836 : UInt32).toNat ] ptr0 ∗ n ↦[i32][ (1051836 : UInt32).toNat + 4 ] 0 ∗
    n ↦[i32][ (1065404 : UInt32).toNat + 12 ] 157 ∗ ta ↦[wt][ (157 : UInt32).toNat ] Ref.func a759 ∗
    ta ↦[wt][ (92 : UInt32).toNat ] Ref.func a353)

theorem frame64_open (n a : Nat) :
    stk (GF := GF) n a 64 ⊢ stk n a 8 ∗ stk n (a + 8) 8 ∗ stk n (a + 16) 8 ∗ stk n (a + 24) 4 ∗
      stk n (a + 28) 4 ∗ stk n (a + 32) 4 ∗ stk n (a + 36) 8 ∗ stk n (a + 44) 4 ∗ stk n (a + 48) 4 ∗
      stk n (a + 52) 4 ∗ stk n (a + 56) 8 := by
  iintro H
  icases stk_split n a 8 56 $$ H with ⟨H0, H⟩
  icases stk_split n (a + 8) 8 48 $$ H with ⟨H1, H⟩
  icases stk_split n (a + 8 + 8) 8 40 $$ H with ⟨H2, H⟩
  icases stk_split n (a + 8 + 8 + 8) 4 36 $$ H with ⟨H3, H⟩
  icases stk_split n (a + 8 + 8 + 8 + 4) 4 32 $$ H with ⟨H4, H⟩
  icases stk_split n (a + 8 + 8 + 8 + 4 + 4) 4 28 $$ H with ⟨H5, H⟩
  icases stk_split n (a + 8 + 8 + 8 + 4 + 4 + 4) 8 20 $$ H with ⟨H6, H⟩
  icases stk_split n (a + 8 + 8 + 8 + 4 + 4 + 4 + 8) 4 16 $$ H with ⟨H7, H⟩
  icases stk_split n (a + 8 + 8 + 8 + 4 + 4 + 4 + 8 + 4) 4 12 $$ H with ⟨H8, H⟩
  icases stk_split n (a + 8 + 8 + 8 + 4 + 4 + 4 + 8 + 4 + 4) 4 8 $$ H with ⟨H9, H10⟩
  iframe H0 H1
  rw [show a + 8 + 8 = a + 16 by omega, show a + 16 + 8 = a + 24 by omega,
    show a + 24 + 4 = a + 28 by omega, show a + 28 + 4 = a + 32 by omega,
    show a + 32 + 4 = a + 36 by omega, show a + 36 + 8 = a + 44 by omega,
    show a + 44 + 4 = a + 48 by omega, show a + 48 + 4 = a + 52 by omega,
    show a + 52 + 4 = a + 56 by omega]
  iframe H2 H3 H4 H5 H6 H7 H8 H9 H10

theorem frame64_close (n a : Nat) :
    stk (GF := GF) n a 8 ∗ stk n (a + 8) 8 ∗ stk n (a + 16) 8 ∗ stk n (a + 24) 4 ∗
      stk n (a + 28) 4 ∗ stk n (a + 32) 4 ∗ stk n (a + 36) 8 ∗ stk n (a + 44) 4 ∗ stk n (a + 48) 4 ∗
      stk n (a + 52) 4 ∗ stk n (a + 56) 8 ⊢ stk n a 64 := by
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  ihave H := stk_join n (a + 52) 4 8 $$ [H9 H10]
  · iframe H9; iexact H10
  ihave H := stk_join n (a + 48) 4 12 $$ [H8 H]
  · iframe H8; iexact H
  ihave H := stk_join n (a + 44) 4 16 $$ [H7 H]
  · iframe H7; iexact H
  ihave H := stk_join n (a + 36) 8 20 $$ [H6 H]
  · iframe H6; iexact H
  ihave H := stk_join n (a + 32) 4 28 $$ [H5 H]
  · iframe H5; iexact H
  ihave H := stk_join n (a + 28) 4 32 $$ [H4 H]
  · iframe H4; iexact H
  ihave H := stk_join n (a + 24) 4 36 $$ [H3 H]
  · iframe H3; iexact H
  ihave H := stk_join n (a + 16) 8 40 $$ [H2 H]
  · iframe H2; iexact H
  ihave H := stk_join n (a + 8) 8 48 $$ [H1 H]
  · iframe H1; iexact H
  iapply stk_join n a 8 56
  iframe H0 H

theorem i64_one : storeBytes (.i64 1) 8 = bytes32 1 ++ bytes32 0 := by decide

theorem hb32 (v : UInt32) : (bytes32 v).length = 4 := by simp [bytes32]

theorem w2 (n a : Nat) (x y : UInt32) :
    n ↦[i32][ a ] x ∗ n ↦[i32][ a + 4 ] y ⊢ stk (GF := GF) n a 8 := by
  iintro ⟨H0, H4⟩
  iapply FmtU128.stk_of n a 8 (bytes32 x ++ bytes32 y) (by simp [hb32])
  iapply (memBytes_append (GF := GF) (H := NearState) n a (bytes32 x) (bytes32 y)).2
  rw [hb32]
  iframe H0 H4

theorem newCap_ge (k : UInt32) : k.toNat ≤ (newCap 0 k).toNat ∧ 8 ≤ (newCap 0 k).toNat := by
  unfold newCap
  split <;> simp_all <;> omega

theorem tbl_addr {ta i j : Nat} {r : Ref} (h : i = j) : ta ↦[wt][ i ] r ⊢ (ta ↦[wt][ j ] r : IProp GF) := by
  subst h; exact .rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem f385_gen (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 25 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s v ser ptr0 aidx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat)) (lo hi : UInt64)
    (hs : 400 ≤ s.toNat) (hv : v.toNat + 16 ≤ 2 ^ 32) (hr : roomFor hl maxP (newCap 0 (kOf (val lo hi))))
    (P Q : IProp GF) (K : Nat) :
    tsCode n maxP inst mi A ∗
      (□ ∀ q : UInt32, ⌜q ≠ 0 ∧ q.toNat + (newCap 0 (kOf (val lo hi))).toNat < 2 ^ 32⌝ -∗
        MFunSpec cfg lim (d + 1) types[15]! inst mi f383 Cg
          (fun args => iprop(⌜args = [.i32 ser, .i32 q, .i32 (kOf (val lo hi))]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 64)⟩ ∗
            stk n ((s - 64).toNat - 336) 336 ∗ n ↦[wms][ q.toNat ] decDigits (val lo hi) ∗ P))
          (fun _ => K)
          (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 64)⟩ ∗
            stk n ((s - 64).toNat - 336) 336 ∗ n ↦[wms][ q.toNat ] decDigits (val lo hi) ∗ Q)))
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f385 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 ser]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 400) 400 ∗
          tsData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live 1 ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut ∗ P))
        (fun _ => 1000 * cfg.regularOpCost + cost746 cfg lo hi + K)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 400) 400 ∗
          tsData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗
          (∃ hl', heapInv n maxP hl' live 2) ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut ∗ Q)) := by
  iintro ⟨#Hk, #S383⟩
  have hn := hm.mem
  have hg := hm.glob
  have hlt := s.toNat_lt
  have hsp : (s - 64).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h8 : (s - 64 + 8).toNat = (s - 64).toNat + 8 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have h16 : (s - 64 + 16).toNat = (s - 64).toNat + 16 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have h28 : (s - 64 + 28).toNat = (s - 64).toNat + 28 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have h32 : (s - 64 + 32).toNat = (s - 64).toNat + 32 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have h56 : (s - 64 + 56).toNat = (s - 64).toNat + 56 := by rw [UInt32.toNat_add, hsp]; simp; omega
  have ha746 := hm.funcs 746 (by decide)
  have ha472 := hm.funcs 472 (by decide)
  have ha365 := hm.funcs 365 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have ha383 := hm.funcs 383 (by decide)
  have ha321 := hm.funcs 321 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, HD, Hvt, Hh, Hv, Hl, HP⟩
  subst hargs
  simp only [f385]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  iunfold tsCode at Hk
  icases Hk with ⟨#Hfc, #H901, #H353, #H872, #Hsc, #Hdc, #H746, #H472, #H365, #H779, #H383, #H321⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hdc; icases Hdc with ⟨#Hi, -⟩; iexact Hi
  icases (stk_split n (s.toNat - 400) 336 64) $$ Hs with ⟨Hb, Hs⟩
  ihave Hs := stk_addr (show s.toNat - 400 + 336 = (s - 64).toNat by omega) $$ Hs
  icases frame64_open n (s - 64).toNat $$ Hs with ⟨O0, O8, O16, O24, O28, O32, O36, O44, O48, O52, O56⟩
  iunfold stk at O8 O16 O24 O28 O32 O36 O48 O52 O56
  icases O8 with ⟨%o8, %ho8, O8⟩
  icases O16 with ⟨%o16, %ho16, O16⟩
  icases O24 with ⟨%o24, %ho24, O24⟩
  icases O28 with ⟨%o28, %ho28, O28⟩
  icases O32 with ⟨%o32, %ho32, O32⟩
  icases O36 with ⟨%o36, %ho36, O36⟩
  icases O48 with ⟨%o48, %ho48, O48⟩
  icases O52 with ⟨%o52, %ho52, O52⟩
  icases O56 with ⟨%o56, %ho56, O56⟩
  mstep; mstep; mstep [O24]
  mstep; mstep; mstep [O16]
  mstep; mstep; mstep [O28]
  rw [i64_one]
  repeat mstep
  ihave O8 := memBytes_addr (show (s - 64).toNat + 8 = (s - 64 + 8).toNat by rw [h8]) $$ O8
  mcall (SerdeLeaves.f472_spec cfg lim (d + 1) types[31]! rfl inst mi n hn Cg (s - 64 + 8) (s - 64 + 28) 92 o8 ho8
    (by rw [h8]; omega)) using [O8]
  · iframe O8
  icases HQ with ⟨%hrs, W8, W12⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep [O52]
  mstep; mstep; mstep [O36]
  mstep; mstep; mstep [O32]
  rw [i64_one]
  ihave L8 := (memBytes_append (GF := GF) (H := NearState) n ((s - 64).toNat + 8) (bytes32 (s - 64 + 28)) (bytes32 92)).2 $$ [W8 W12]
  · rw [hb32]
    isplitl [W8]; · iapply memBytes_addr h8 $$ W8
    iapply memBytes_addr (show (s - 64 + 8).toNat + 4 = (s - 64).toNat + 8 + 4 by omega) $$ W12
  mstep; mstep; mstep [L8]
  mstep [O56]
  rw [ResultExpect.bytes64_decode _ (by simp [hb32])]
  repeat mstep
  mstep [O48]
  repeat mstep
  iunfold stk at O44
  icases O44 with ⟨%junk, %hjunk, O44⟩
  have hs96 : (s - 64 - 32).toNat = s.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le, hsp] <;> omega
  icases (stk_split n (s.toNat - 400) 304 32) $$ Hb with ⟨Hb1, Hb2⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 64).toNat + 36) (bytes32 1) (bytes32 0)).1 $$ O36
    with ⟨A4, A8⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 64).toNat + 56) (bytes32 (s - 64 + 28)) (bytes32 92)).1 $$ O56
    with ⟨G0, G4⟩
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 64).toNat + 16) (bytes32 1) (bytes32 0)).1 $$ O16
    with ⟨V0, V4⟩
  simp only [hb32]
  iunfold tsData at HD
  icases HD with ⟨D0, D4, D12, T157, T92⟩
  mcall (f746_u128 cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 64) (s - 64 + 32)
      (s - 64 + 16) aidx (s - 64 + 56) (s - 64 + 28) v ptr0 junk hjunk maxP hl live lo hi (by omega)
      (by rw [h32]; omega) (by rw [h16]; omega) (by rw [h56]; omega) (by rw [h28]; omega) hv hr)
    using [Hg Hb1 Hb2 O32 A4 A8 O48 O52 O44 D0 D4 D12 T157 T92 G0 G4 Hvt Hh V0 V4 O24 O28 Hv Hl]
  · iframe Hg
    isplitl [Hb2]; · iapply stk_addr (show s.toNat - 400 + 304 = (s - 64).toNat - 32 by omega) $$ Hb2
    isplitl [O32 A4 A8 O48 O52]
    · iunfold argsAt
      isplitl [O32]; · iapply memBytes_addr (by omega) $$ O32
      isplitl [A4]; · iapply memBytes_addr (by omega) $$ A4
      isplitl [A8]; · iapply memBytes_addr (by omega) $$ A8
      isplitl [O48]; · iapply memBytes_addr (by omega) $$ O48
      iapply memBytes_addr (by omega) $$ O52
    isplitl [O44]; · iapply memBytes_addr (by omega) $$ O44
    iunfold fIn
    isplitl [Hb1]; · iapply stk_addr (show s.toNat - 400 = (s - 64 - 32).toNat - 304 by omega) $$ Hb1
    iframe Hvt Hh Hv Hl
    isplitl [D0 D4 G0 G4 T92]
    · iunfold pieceArg
      isplitl [D0]; · iapply memBytes_addr (by first | rfl | simp) $$ D0
      isplitl [D4]; · iapply memBytes_addr (by first | rfl | simp) $$ D4
      isplitl [G0]; · iapply memBytes_addr (by omega) $$ G0
      isplitl [G4]; · iapply memBytes_addr (by omega) $$ G4
      iapply tbl_addr (by first | rfl | simp) $$ T92
    isplitl [D12]; · iapply memBytes_addr (by first | rfl | simp) $$ D12
    isplitl [T157]; · iapply tbl_addr (by first | rfl | simp) $$ T157
    isplitl [V0]; · iapply memBytes_addr (by omega) $$ V0
    isplitl [V4]; · iapply memBytes_addr (by omega) $$ V4
    isplitl [O24]; · iapply memBytes_addr (by omega) $$ O24
    iapply memBytes_addr (by omega) $$ O28
  icases HQ with ⟨%hrs, Hg, Hb2, HA, O44, HF⟩
  subst hrs
  mcall (SerdeLeaves.f365_ok cfg lim (d + 1) types[0]! rfl inst mi g hg Cg gt (s - 64)) using [Hg]
  · iframe Hg
  icases HQ with ⟨%hrs, Hg⟩
  subst hrs
  iunfold fOut at HF
  icases HF with ⟨Hb1, HPA, D12, T157, Hvt, Hsg, Hvp, Hv, Hl⟩
  iunfold strGrown at Hsg
  icases Hsg with ⟨%q, %⟨hq0, hqc⟩, V0, V4, V8, Hds, Hrest, Hgr⟩
  ihave Vb := (memBytes_append (GF := GF) (H := NearState) n (s - 64 + 16).toNat
    (bytes32 q) (bytes32 (newCap 0 (kOf (val lo hi))) ++ bytes32 (kOf (val lo hi)))).2 $$ [V0 V4 V8]
  · iframe V0
    iapply (memBytes_append (GF := GF) (H := NearState) n _ _ _).2
    simp only [hb32]
    isplitl [V4]; · iapply memBytes_addr (by omega) $$ V4
    iapply memBytes_addr (by omega) $$ V8
  iunfold stk at O0
  icases O0 with ⟨%o0, %ho0, O0⟩
  repeat mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 64) (s - 64 + 16) o0
    (bytes32 q ++ (bytes32 (newCap 0 (kOf (val lo hi))) ++ bytes32 (kOf (val lo hi)))) ho0
    (by simp [hb32])) using [O0 Vb]
  · iunfold VecDeref.pre
    iframe Vb
    isplitr [O0]; · ipureintro; rfl
    iapply memBytes_addr (by omega) $$ O0
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, O0, Vb⟩
  subst hrs
  have e0 : List.take 4 (bytes32 q ++ (bytes32 (newCap 0 (kOf (val lo hi))) ++ bytes32 (kOf (val lo hi)))) ++
      List.drop 8 (bytes32 q ++ (bytes32 (newCap 0 (kOf (val lo hi))) ++ bytes32 (kOf (val lo hi)))) =
      bytes32 q ++ bytes32 (kOf (val lo hi)) := by
    first | rfl | simp [bytes32, List.range_succ]
  rw [e0]
  icases (memBytes_append (GF := GF) (H := NearState) n ((s - 64).toNat) (bytes32 q) (bytes32 (kOf (val lo hi)))).1 $$ O0
    with ⟨Q0, Q4⟩
  simp only [hb32]
  mstep; mstep; mstep [Q0]
  mstep; mstep [Q4]
  repeat mstep
  ihave #S3 := S383 $$ %q %⟨hq0, hqc⟩
  ihave Hb : stk n ((s - 64).toNat - 336) 336 $$ [Hb1 Hb2]
  · iapply stk_join n ((s - 64).toNat - 336) 304 32
    isplitl [Hb1]; · iapply stk_addr (show (s - 64 - 32).toNat - 304 = (s - 64).toNat - 336 by omega) $$ Hb1
    iapply stk_addr (show (s - 64).toNat - 32 = (s - 64).toNat - 336 + 304 by omega) $$ Hb2
  mcall S3 using [Hg Hb Hds HP]
  · iframe Hg Hb Hds HP
  icases HQ with ⟨%hrs, Hg, Hb, Hds, HQ⟩
  subst hrs
  repeat mstep
  -- the String's buffer, as a block; its words
  have hk := newCap_ge (kOf (val lo hi))
  icases Hrest with ⟨%rest, %hrest, Hrest⟩
  ihave Hblk : block n q.toNat (newCap 0 (kOf (val lo hi))).toNat $$ [Hds Hrest]
  · iunfold block
    iexists decDigits (val lo hi) ++ rest
    isplitr
    · ipureintro; simp [hrest, ← FmtString.kOf_toNat lo hi]; omega
    iapply (memBytes_append (GF := GF) (H := NearState) n _ _ _).2
    iframe Hds
    rw [← FmtString.kOf_toNat lo hi]
    iexact Hrest
  iunfold grown at Hgr
  icases Hgr with ⟨%hl', %hhl, Hh⟩
  icases (memBytes_append (GF := GF) (H := NearState) n (s - 64 + 16).toNat (bytes32 q) _).1 $$ Vb with ⟨W0, Vb⟩
  icases (memBytes_append (GF := GF) (H := NearState) n _ (bytes32 (newCap 0 (kOf (val lo hi)))) _).1 $$ Vb
    with ⟨W4, W8⟩
  simp only [hb32]
  mcall (SerdeLeaves.f321_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl'
      ((q.toNat, (newCap 0 (kOf (val lo hi))).toNat) :: live) 1 (s - 64 + 16) q (newCap 0 (kOf (val lo hi)))
      (kOf (val lo hi)) (fun h => by rw [h] at hk; simp at hk) (by rw [h16]; omega)) using [W0 W4 W8 Hh Hblk]
  · iunfold pre747
    isplitr; · ipureintro; rfl
    iframe W0 Hh Hblk
    isplitl [W4]; · iapply memBytes_addr (by omega) $$ W4
    isplitl [W8]; · iapply memBytes_addr (by omega) $$ W8
    ipureintro; simp
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, W0, W4, W8, Hh⟩
  subst hrs
  repeat mstep
  rw [show s - 64 + 64 = s by simp]
  mstep [Hg]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt Hv Hl HQ
  isplitr; · ipureintro; rw [htype]; rfl
  iunfold argsAt at HA
  icases HA with ⟨A0, A4, A8, A16, A20⟩
  iunfold pieceArg at HPA
  icases HPA with ⟨D0, D4, G0, G4, T92⟩
  isplitl [Hb Q0 Q4 L8 W0 W4 W8 Hvp A0 A4 A8 O44 A16 A20 G0 G4]
  · iapply stk_addr (show (s - 64).toNat - 336 = s.toNat - 400 by omega)
    iapply stk_join n ((s - 64).toNat - 336) 336 64
    iframe Hb
    iapply stk_addr (show (s - 64).toNat = (s - 64).toNat - 336 + 336 by omega)
    iapply frame64_close n (s - 64).toNat
    isplitl [Q0 Q4]; · iapply w2; iframe Q0 Q4
    isplitl [L8]; · iapply FmtU128.stk_of n _ 8 _ (by simp [hb32]) $$ L8
    isplitl [W0 W4]
    · iapply w2
      isplitl [W0]; · iapply memBytes_addr (by omega) $$ W0
      iapply memBytes_addr (by omega) $$ W4
    isplitl [W8]; · iapply stk_word; iapply memBytes_addr (by omega) $$ W8
    isplitl [Hvp]; · iapply stk_word; iapply memBytes_addr (by omega) $$ Hvp
    isplitl [A0]; · iapply stk_word; iapply memBytes_addr (by omega) $$ A0
    isplitl [A4 A8]
    · iapply w2
      isplitl [A4]; · iapply memBytes_addr (by omega) $$ A4
      iapply memBytes_addr (by omega) $$ A8
    isplitl [O44]; · iapply FmtU128.stk_of n _ 4 _ hjunk; iapply memBytes_addr (by omega) $$ O44
    isplitl [A16]; · iapply stk_word; iapply memBytes_addr (by omega) $$ A16
    isplitl [A20]; · iapply stk_word; iapply memBytes_addr (by omega) $$ A20
    iapply w2
    isplitl [G0]; · iapply memBytes_addr (by omega) $$ G0
    iapply memBytes_addr (by omega) $$ G4
  isplitl [D0 D4 D12 T157 T92]
  · iunfold tsData
    isplitl [D0]; · iapply memBytes_addr (by first | rfl | simp) $$ D0
    isplitl [D4]; · iapply memBytes_addr (by first | rfl | simp) $$ D4
    isplitl [D12]; · iapply memBytes_addr (by first | rfl | simp) $$ D12
    isplitl [T157]; · iapply tbl_addr (by first | rfl | simp) $$ T157
    iapply tbl_addr (by first | rfl | simp) $$ T92
  iexists hl'
  simp only [List.erase_cons_head]
  iexact Hh

end Spec
section Digits

open WNear.Binary.SerializeStr (AllDigits esc serCode cost383 f383_digits)

theorem decDigits_all (N : Nat) : AllDigits (decDigits N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hd : ∀ m, m < 10 → AllDigits [FmtDigits.digit m] := by
      intro m hm b hb
      simp at hb; subst hb
      simp [FmtDigits.digit]; omega
    rw [FmtDigits.decDigits]
    split
    · exact hd N (by omega)
    · intro b hb
      rcases List.mem_append.mp hb with h | h
      · exact ih (N / 10) (by omega) b h
      · exact hd (N % 10) (by omega) b h

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The serializer's output (owned): the quote and the `ESCAPE` entries of the digits (data),
`*ser = ovec`, the empty `Vec` `(optr, 128, 0)` at `ovec` and its 128 bytes. -/
def serIn (n : Nat) (ser ovec optr : UInt32) (ob : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061856 ] esc ∗ n ↦[i32][ ser.toNat ] ovec ∗
    n ↦[i32][ ovec.toNat ] optr ∗ n ↦[i32][ ovec.toNat + 4 ] 128 ∗ n ↦[i32][ ovec.toNat + 8 ] 0 ∗
    n ↦[wms][ optr.toNat ] ob)

/-- After: the JSON string of the digits `ds` (`k` of them) at the front of the buffer. -/
def serOut (n : Nat) (ser ovec optr : UInt32) (ob : List UInt8) (k : UInt32) (ds : List UInt8) : IProp GF :=
  iprop(n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061856 ] esc ∗ n ↦[i32][ ser.toNat ] ovec ∗
    n ↦[i32][ ovec.toNat ] optr ∗ n ↦[i32][ ovec.toNat + 4 ] 128 ∗ n ↦[i32][ ovec.toNat + 8 ] (0 + k + 2) ∗
    n ↦[wms][ optr.toNat ] (([34] ++ ds ++ [34]) ++ ob.drop (k.toNat + 2)))

/-- The cost of `<U128 as Serialize>::serialize` (385), activation excluded. -/
noncomputable def cost385 (cfg : WasmConfig) (lo hi : UInt64) : Nat :=
  1000 * cfg.regularOpCost + cost746 cfg lo hi + cost383 (kOf (val lo hi)).toNat * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`<U128 as Serialize>::serialize(v, ser)`** (385) of the `u128` at `v` into the serializer
`ser` writing to the empty `Vec` `(optr, 128, 0)`: `Ok`, the buffer starting with the JSON
string of the decimal digits; the heap gets back its live blocks. -/
theorem f385_u128 (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 25 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s v ser ptr0 aidx ovec optr : UInt32) (ob : List UInt8) (maxP hl : Nat) (live : List (Nat × Nat))
    (lo hi : UInt64) (hs : 400 ≤ s.toNat) (hv : v.toNat + 16 ≤ 2 ^ 32)
    (hr : roomFor hl maxP (newCap 0 (kOf (val lo hi)))) (hob : ob.length = 128)
    (hser : ser.toNat + 4 ≤ 2 ^ 32) (hovec : ovec.toNat + 12 ≤ 2 ^ 32) (hoptr : optr.toNat + 128 < 2 ^ 32) :
    tsCode n maxP inst mi A ∗ serCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f385 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 ser]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 400) 400 ∗
          tsData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live 1 ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut ∗ serIn n ser ovec optr ob))
        (fun _ => cost385 cfg lo hi)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 400) 400 ∗
          tsData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗
          (∃ hl', heapInv n maxP hl' live 2) ∗
          n ↦[wms][ v.toNat ] u128Bytes lo hi ∗ n ↦[wms][ 1070974 ] lut ∗
          serOut n ser ovec optr ob (kOf (val lo hi)) (decDigits (val lo hi)))) := by
  iintro ⟨#Hk, #Hs⟩
  have hlt := s.toNat_lt
  have hsp : (s - 64).toNat = s.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hK := FmtString.kOf_toNat lo hi
  have hL1 := FmtString.decDigits_le lo hi
  have hL2 := FmtDigits.decDigits_length_pos (val lo hi)
  have hk := newCap_ge (kOf (val lo hi))
  iunfold cost385
  iapply f385_gen cfg lim d type htype inst mi A n g ta hm hd Cg gt s v ser ptr0 aidx maxP hl live lo hi hs hv hr
  iframe Hk
  imodintro
  iintro %q %⟨hq0, hqc⟩
  iapply AllocFresh.MFunSpec_frame
    (Fr := iprop(stk n ((s - 64).toNat - 336) 288 ∗
      n ↦[wms][ optr.toNat + ((kOf (val lo hi)).toNat + 2) ] ob.drop ((kOf (val lo hi)).toNat + 2)))
    (P := fun args => iprop(⌜args = [.i32 ser, .i32 q, .i32 (kOf (val lo hi))]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 64)⟩ ∗
      stk n ((s - 64).toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061856 ] esc ∗
      n ↦[i32][ ser.toNat ] ovec ∗ n ↦[i32][ ovec.toNat ] optr ∗ n ↦[i32][ ovec.toNat + 4 ] (128 : UInt32) ∗
      n ↦[i32][ ovec.toNat + 8 ] (0 : UInt32) ∗
      n ↦[wms][ optr.toNat + (0 : UInt32).toNat ] (ob.take ((kOf (val lo hi)).toNat + 2)) ∗
      n ↦[wms][ q.toNat ] decDigits (val lo hi)))
    (Q := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 (s - 64)⟩ ∗
      stk n ((s - 64).toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061856 ] esc ∗
      n ↦[i32][ ser.toNat ] ovec ∗ n ↦[i32][ ovec.toNat ] optr ∗ n ↦[i32][ ovec.toNat + 4 ] (128 : UInt32) ∗
      n ↦[i32][ ovec.toNat + 8 ] ((0 : UInt32) + kOf (val lo hi) + 2) ∗
      n ↦[wms][ optr.toNat + (0 : UInt32).toNat ] ([34] ++ decDigits (val lo hi) ++ [34]) ∗
      n ↦[wms][ q.toNat ] decDigits (val lo hi)))
  · intro args
    iintro ⟨%ha, Hg, Hb, Hds, HP⟩
    iunfold serIn at HP
    icases HP with ⟨Hq, He, Hser, V0, V4, V8, Hob⟩
    icases stk_split n ((s - 64).toNat - 336) 288 48 $$ Hb with ⟨Hb1, Hb2⟩
    icases U128From.memBytes_split n optr.toNat ((kOf (val lo hi)).toNat + 2) ob (by omega) $$ Hob with ⟨Ho1, Ho2⟩
    iframe Hb1 Ho2
    isplitr; · ipureintro; exact ha
    iframe Hg Hq He Hser V0 V4 V8 Hds
    isplitl [Hb2]
    · iapply stk_addr (show (s - 64).toNat - 336 + 288 = (s - 64).toNat - 48 by omega) $$ Hb2
    iapply memBytes_addr (show optr.toNat = optr.toNat + (0 : UInt32).toNat by simp) $$ Ho1
  · intro args rs
    iintro ⟨⟨Hb1, Ho2⟩, %hrs, Hg, Hb2, Hq, He, Hser, V0, V4, V8, Ho1, Hds⟩
    iframe Hg Hds
    isplitr; · ipureintro; exact hrs
    isplitl [Hb1 Hb2]
    · iapply stk_join n ((s - 64).toNat - 336) 288 48
      iframe Hb1
      iapply stk_addr (show (s - 64).toNat - 48 = (s - 64).toNat - 336 + 288 by omega) $$ Hb2
    iunfold serOut
    iframe Hq He Hser V0 V4 V8
    iapply (memBytes_append (GF := GF) (H := NearState) n optr.toNat _ _).2
    isplitl [Ho1]; · iapply memBytes_addr (show optr.toNat + (0 : UInt32).toNat = optr.toNat by simp) $$ Ho1
    iapply memBytes_addr (by simp [hK]) $$ Ho2
  iapply f383_digits cfg lim (d + 1) types[15]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 64) ser ovec
    optr 128 0 q (kOf (val lo hi)) (ob.take ((kOf (val lo hi)).toNat + 2)) (decDigits (val lo hi)) (by omega)
    (by simp; omega) (by omega) (by omega) (decDigits_all _) hser hovec (by simp; omega) (by simp; omega)
    (by omega)
  iexact Hs

end Digits

end WNear.Binary.ToString
