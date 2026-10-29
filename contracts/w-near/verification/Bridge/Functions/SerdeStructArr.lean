import Bridge.Functions.SerdeSeqElem
import Bridge.Functions.SerdeEndSeq

/-!
# `deserialize_struct` (228) for `ft_balance_of`'s arguments: the array form (M6)

228 reads the struct `{ account_id }` from `{ ... }` or from `[ ... ]`. This file proves its
accepting run on the array form `["<a>"]`, the struct's one element read by
`ValidAccountId::deserialize` (169), taken as the hypothesis `Hyp169`:

```wat
;; 228 (out, de, …)   ws (339); '[' →
;;   remaining_depth -= 1 (128 → 127; 0 → RecursionLimitExceeded)
;;   eat '[' (333); SeqAccess (de, first = 1) at sp+40
;;   next_element_seed (214) into sp+8: Ok(Some(v)) → remaining_depth += 1, end_seq (91) → 0
;;   out := Ok(v)
```

* `Hyp169` is 169's accepting specification against a reader `dv` of account ids (in the sense of
  `SerdeStructModel.fromSlice`): where `dv (bs.drop j) = some (a, r)`, 169 returns `Ok(String)`
  with `a`'s bytes in a fresh block, the reader at `|bs| - |r|`, the heap with room left for an
  error box (`strRes`).
* `f228_arr`: on an input whose struct is in the array form and accepted
  (`skipWhitespace = [ …`, the element not `]`, `dv` reads it, then `]`), `out` holds `Ok(a)`.
-/

namespace WNear.Binary.SerdeStructArr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode some_bit)
open WNear.Binary.SerdeSeqElem (Spec169)

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The account id `a` read by 169: its `String (p, cap, |a|)` owns `a`'s bytes at `p` and the rest
of a block the heap lends (`(p, cap)` in front of `live`), and the heap still has room for an error
box. -/
def strRes (n maxP : Nat) (live : List (Nat × Nat)) (a : WNear.AccountId) (p cap : UInt32) : IProp GF :=
  iprop(∃ (mlen F : Nat), ⌜p ≠ 0 ∧ a.val.utf8ByteSize ≤ cap.toNat ∧ roomFor4 mlen maxP 20⌝ ∗
    n ↦[wms][ p.toNat ] a.val.toUTF8.toList ∗ block n (p.toNat + a.val.utf8ByteSize) (cap.toNat - a.val.utf8ByteSize) ∗
    heapInv n maxP mlen ((p.toNat, cap.toNat) :: live) F)

/-- The tables and the scratch's length the string readers use. -/
def tbl (n : Nat) (de : UInt32) : IProp GF :=
  iprop((∃ sl : UInt32, n ↦[i32][ de.toNat + 20 ] sl) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
    n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width)

end Defs

/-- **The hypothesis on 169** (`ValidAccountId::deserialize`), for the reader `dv`, the cost
`K169 j` at the index `j`: wherever `dv` reads an account id `a` from `j`, leaving `r`, 169 called
at `j` returns `Ok(String)` holding `a` (`strRes`), the reader at `|bs| - |r|`. Its stack is 256
bytes. -/
def Hyp169 {GF : BundledGFunctors} [WasmGS NearState GF] (cfg : WasmConfig) (lim : ExecLimits)
    (inst : Nat) (mi : ModuleInst) (n g ta : Nat) (A : Nat → Nat) (Cg : Nat) (gt : GlobalType)
    (de ptr idx : UInt32) (bs : List UInt8) (maxP : Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (K169 : Nat → Nat) (Cd : IProp GF) : Prop :=
  ∀ (d : Nat) (sp out : UInt32) (ob : List UInt8) (j : Nat) (a : WNear.AccountId) (r : List UInt8)
    (mlen F : Nat) (live : List (Nat × Nat)),
    d + 16 < lim.maxCallDepth → ob.length = 16 → out.toNat + 16 ≤ 2 ^ 32 → 256 ≤ sp.toNat →
    j ≤ bs.length → roomFor4 mlen maxP 20 → dv (bs.drop j) = some (a, r) →
    Cd ⊢ MFunSpec (GF := GF) cfg lim d types[14]! inst mi f169 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 256) 256 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs j ∗ tbl n de))
        (fun _ => K169 j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 256) 256 ∗
          vt n 1057464 idx ta (A 578) ∗ tbl n de ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap ∗ rd n de ptr bs (bs.length - r.length)))

section L228

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem strRes_ne (n maxP : Nat) (live : List (Nat × Nat)) (a : WNear.AccountId) (p cap : UInt32) :
    strRes (GF := GF) n maxP live a p cap ⊢ ⌜p ≠ 0⌝ ∗ strRes n maxP live a p cap := by
  iintro H
  iunfold strRes at H
  icases H with ⟨%m, %F, %⟨hp, h1, h2⟩, H1, H2, H3⟩
  isplitr
  · ipureintro; exact hp
  iunfold strRes
  iexists m
  iexists F
  iframe H1 H2 H3
  ipureintro; exact ⟨hp, h1, h2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `SerdeSeqElem.Spec169` (214's view of 169, its frame at `sp - 16`) from `Hyp169`. -/
theorem spec169_of_hyp (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (n g ta : Nat)
    (A : Nat → Nat) (Cg : Nat) (gt : GlobalType) (de ptr idx : UInt32) (bs : List UInt8) (maxP : Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (K169 : Nat → Nat) (Cd : IProp GF)
    [Persistent Cd] (h : Hyp169 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP dv K169 Cd)
    (d : Nat) (hd : d + 16 < lim.maxCallDepth) (sp : UInt32) (ob : List UInt8) (hob : ob.length = 16)
    (hsp : 272 ≤ sp.toNat) (j : Nat) (a : WNear.AccountId) (r : List UInt8) (hj : j ≤ bs.length)
    (mlen F : Nat) (live : List (Nat × Nat)) (hr : roomFor4 mlen maxP 20) (hdv : dv (bs.drop j) = some (a, r)) :
    Cd ⊢ Spec169 cfg lim d inst mi n g Cg gt sp de ptr ob bs j
      iprop(stk n (sp.toNat - 272) 256 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ tbl n de)
      (K169 j)
      (fun p c l => iprop(⌜l = UInt32.ofNat a.val.utf8ByteSize⌝ ∗ stk n (sp.toNat - 272) 256 ∗
        vt n 1057464 idx ta (A 578) ∗ tbl n de ∗ strRes n maxP live a p c ∗
        rd n de ptr bs (bs.length - r.length))) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have s := h d (sp - 16) (sp - 16) ob j a r mlen F live hd hob (by omega) (by omega) hj hr hdv
  rw [show (sp - 16).toNat - 256 = sp.toNat - 272 by omega] at s
  iintro #HC
  ihave #S := s $$ HC
  clear s
  iunfold Spec169
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 (sp - 16), .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗
          stk n (sp.toNat - 272) 256 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗
          n ↦[wms][ (sp - 16).toNat ] ob ∗ rd n de ptr bs j ∗ tbl n de))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n (sp.toNat - 272) 256 ∗
          vt n 1057464 idx ta (A 578) ∗ tbl n de ∗
          ∃ (p cap : UInt32), n ↦[i32][ (sp - 16).toNat ] 0 ∗ n ↦[i32][ (sp - 16).toNat + 4 ] p ∗
            n ↦[i32][ (sp - 16).toNat + 8 ] cap ∗ n ↦[i32][ (sp - 16).toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap ∗ rd n de ptr bs (bs.length - r.length))) ?hP ?hQ)
  case hP =>
    intro args
    iintro ⟨%ha, Hg, Ho, Hrd, Hs, Hvt, Hh, Ht⟩
    iframe Hg Ho Hrd Hs Hvt Hh Ht
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨-, %hrs, Hg, Hs, Hvt, Ht, %p, %cap, W0, W4, W8, W12, Hstr, Hrd⟩
    ihave Hstr := strRes_ne $$ Hstr
    icases Hstr with ⟨%hp, Hstr⟩
    iframe Hg
    isplitr
    · ipureintro; exact hrs
    iexists p
    iexists cap
    iexists UInt32.ofNat a.val.utf8ByteSize
    isplitr
    · ipureintro; exact hp
    iframe W0 W4 W8 W12
    isplitr
    · ipureintro; rfl
    iframe Hs Hvt Ht Hstr Hrd
  iexact S

theorem resSeq_pos {ok : Prop} [Decidable ok] (h : ok) (n maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (de ptr : UInt32) (bs : List UInt8) (k : Nat) (rs : List Value) :
    SerdeEndSeq.resSeq (GF := GF) ok n maxP mlen live F de ptr bs k rs ⊢
      iprop(⌜rs = [.i32 0]⌝ ∗ heapInv n maxP mlen live F ∗ rd n de ptr bs k) := by
  unfold SerdeEndSeq.resSeq; rw [if_pos h]

theorem store1 (n a : Nat) (c : UInt32) (k : UInt8) (h : MemSet.byteOf c = k) :
    n ↦[wms][ a ] (storeBytes (.i32 c) 1) ⊢ (n ↦[wms][ a ] [k] : IProp GF) := by
  rw [MemSet.storeBytes_i32_1, h]

theorem stk_join' (n a b k1 k2 : Nat) (h : b = a + k1) :
    stk (GF := GF) n a k1 ∗ stk n b k2 ⊢ stk n a (k1 + k2) := by
  subst h; exact stk_join n a k1 k2

/-- 228's 64-byte frame, from the pieces the array path leaves. -/
theorem frame64 (n s : Nat) :
    stk (GF := GF) n s 8 ∗ stk n (s + 8) 4 ∗ stk n (s + 12) 4 ∗ stk n (s + 16) 8 ∗ stk n (s + 24) 4 ∗
      stk n (s + 28) 12 ∗ stk n (s + 40) 4 ∗ stk n (s + 44) 1 ∗ stk n (s + 45) 3 ∗ stk n (s + 48) 16 ⊢
      stk n s 64 := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  ihave H9 := stk_join' n (s + 45) (s + 48) 3 16 (by omega) $$ [H9 H10]
  · iframe H9 H10
  ihave H8 := stk_join' n (s + 44) (s + 45) 1 19 (by omega) $$ [H8 H9]
  · iframe H8 H9
  ihave H7 := stk_join' n (s + 40) (s + 44) 4 20 (by omega) $$ [H7 H8]
  · iframe H7 H8
  ihave H6 := stk_join' n (s + 28) (s + 40) 12 24 (by omega) $$ [H6 H7]
  · iframe H6 H7
  ihave H5 := stk_join' n (s + 24) (s + 28) 4 36 (by omega) $$ [H5 H6]
  · iframe H5 H6
  ihave H4 := stk_join' n (s + 16) (s + 24) 8 40 (by omega) $$ [H4 H5]
  · iframe H4 H5
  ihave H3 := stk_join' n (s + 12) (s + 16) 4 48 (by omega) $$ [H3 H4]
  · iframe H3 H4
  ihave H2 := stk_join' n (s + 8) (s + 12) 4 52 (by omega) $$ [H2 H3]
  · iframe H2 H3
  iapply stk_join' n s (s + 8) 8 56 (by omega)
  iframe H1 H2

theorem depth_back : MemSet.byteOf (UInt32.ofNat (if false = true then Numeric.signExtend 32 8 (Memory.decodeLE
    (storeBytes (Value.i32 (UInt32.ofNat (if false = true then Numeric.signExtend 32 8 (Memory.decodeLE [128])
      else Memory.decodeLE [128]) + 4294967295)) 1)) else Memory.decodeLE (storeBytes (Value.i32 (UInt32.ofNat
      (if false = true then Numeric.signExtend 32 8 (Memory.decodeLE [128]) else Memory.decodeLE [128]) +
        4294967295)) 1)) + 1) = 128 := by decide

theorem cost91_ok (cfg : WasmConfig) (F : Nat) (bs : List UInt8) (j : Nat)
    (h : bs[j + wsLen (bs.drop j)]? = some 0x5D) :
    SerdeEndSeq.cost91 cfg F bs j = (400 + 96 * wsLen (bs.drop j)) * cfg.regularOpCost := by
  unfold SerdeEndSeq.cost91
  simp only [h]
  simp

/-- The accepting array form at the reader's index `i`: whitespace, `[`, whitespace, a byte that is
not `]` at `j2`, an account id `a` that `dv` reads from `j2` leaving `r`, whitespace, `]`. -/
def arrOk (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (bs : List UInt8) (i : Nat)
    (a : WNear.AccountId) (r : List UInt8) : Prop :=
  bs[i + wsLen (bs.drop i)]? = some 0x5B ∧
  (∃ b, bs[i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1))]? = some b ∧ b ≠ 0x5D) ∧
  dv (bs.drop (i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)))) = some (a, r) ∧
  bs[bs.length - r.length + wsLen (bs.drop (bs.length - r.length))]? = some 0x5D

/-- The cost of 228 on the array form: `1300·c`, the three runs of whitespace, and 169's. -/
def costArr (cfg : WasmConfig) (K169 : Nat → Nat) (bs : List UInt8) (i : Nat) (r : List UInt8) : Nat :=
  (1300 + 96 * (wsLen (bs.drop i) + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)) +
    wsLen (bs.drop (bs.length - r.length)))) * cfg.regularOpCost +
  K169 (i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **228 on the array form**: `out` gets `Ok(a)`, the `String` `(p, cap, |a|)` (`strRes`), the reader
past the `]`, `remaining_depth` back at 128. -/
theorem f228_arr (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 20 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx x2 x3 x4 x5 : UInt32) (ob bs : List UInt8) (i : Nat)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 25 ≤ 2 ^ 32)
    (hsp : 336 ≤ sp.toNat) (hi : i ≤ bs.length) (hr : roomFor4 mlen maxP 20)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (K169 : Nat → Nat) (Cd : IProp GF)
    [Persistent Cd] (h169 : Hyp169 cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP dv K169 Cd)
    (a : WNear.AccountId) (r : List UInt8) (hok : arrOk dv bs i a r) :
    endCode n maxP inst mi A ∗ A 214 ↪[wf] FuncInst.wasm types[14]! inst f214 ∗
      A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗ A 91 ↪[wf] FuncInst.wasm types[32]! inst f91 ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f228 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de, .i32 x2, .i32 x3, .i32 x4, .i32 x5]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗
          n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de))
        (fun _ => costArr cfg K169 bs i r)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 336) 336 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ de.toNat + 24 ] [128] ∗ tbl n de ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap ∗
            rd n de ptr bs (bs.length - r.length + wsLen (bs.drop (bs.length - r.length)) + 1))) := by
  iintro ⟨#Hv, #F214, #F169, #F91, #HCd⟩
  ihave #Hv' := Hv
  iunfold endCode at Hv'
  icases Hv' with ⟨#Hcode, -, -, #F332, #F333, #F339⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have ha214 := hm.funcs 214 (by decide)
  have ha91 := hm.funcs 91 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  obtain ⟨hb0, ⟨b, hb2, hb93⟩, hdv, hb4⟩ := hok
  unfold costArr
  generalize hw0 : wsLen (bs.drop i) = w0 at hb0 hb2 hdv ⊢
  generalize hj0 : i + w0 = j0 at hb0 hb2 hdv ⊢
  have hj0l := SerdeNextKey.getElem_lt hb0
  generalize hw2 : wsLen (bs.drop (j0 + 1)) = w2 at hb2 hdv ⊢
  generalize hj2 : j0 + 1 + w2 = j2 at hb2 hdv ⊢
  have hj2l := SerdeNextKey.getElem_lt hb2
  generalize hj3 : bs.length - r.length = j3 at hb4 ⊢
  generalize hw4 : wsLen (bs.drop j3) = w4 at hb4 ⊢
  have hj4l := SerdeNextKey.getElem_lt hb4
  generalize hK : K169 j2 = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hrd, Hd, Ht⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  -- the frame and the stack below it
  icases stk_split n (sp.toNat - 336) 256 80 $$ Hs with ⟨S256, S80⟩
  icases stk_split n (sp.toNat - 336 + 256) 16 64 $$ S80 with ⟨S16, F64⟩
  rw [show sp.toNat - 336 + 256 + 16 = (sp - 64).toNat by omega,
    show sp.toNat - 336 + 256 = (sp - 64).toNat - 16 by omega,
    show sp.toNat - 336 = (sp - 64).toNat - 272 by omega]
  icases stk_split n (sp - 64).toNat 8 56 $$ F64 with ⟨X0, F56⟩
  icases stk_split n ((sp - 64).toNat + 8) 16 40 $$ F56 with ⟨R16, F40⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16) 16 24 $$ F40 with ⟨X24, F24⟩
  icases stk_split n ((sp - 64).toNat + 8 + 16 + 16) 8 16 $$ F24 with ⟨A8, X48⟩
  rw [show (sp - 64).toNat + 8 + 16 + 16 + 8 = (sp - 64).toNat + 48 by omega,
    show (sp - 64).toNat + 8 + 16 + 16 = (sp - 64).toNat + 40 by omega,
    show (sp - 64).toNat + 8 + 16 = (sp - 64).toNat + 24 by omega]
  icases stk_split n ((sp - 64).toNat + 24) 4 12 $$ X24 with ⟨X24, X28⟩
  iunfold stk at A8 R16 S16 X24
  icases A8 with ⟨%ba, %hba, A8⟩
  icases R16 with ⟨%ob2, %hob2, R16⟩
  icases S16 with ⟨%ob1, %hob1, S16⟩
  icases X24 with ⟨%bx, %hbx, X24⟩
  icases U128From.memBytes_split n ((sp - 64).toNat + 40) 4 ba (by omega) $$ A8 with ⟨A40, A44⟩
  icases U128From.memBytes_split n ((sp - 64).toNat + 40 + 4) 1 (ba.drop 4) (by simp; omega) $$ A44 with ⟨A44, A45⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
  rw [show (sp - 64).toNat + 40 + 4 = (sp - 64).toNat + 44 by omega, show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  -- the callees
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw0, hj0] at key
  generalize hW0 : (100 + 96 * w0) * cfg.regularOpCost = W0 at key
  have h80 : (sp - 64 - 16).toNat = (sp - 64).toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega
  have hO8 : (sp - 64 + 8).toNat = (sp - 64).toNat + 8 := by simp [UInt32.toNat_add]; omega
  have hA40 : (sp - 64 + 40).toNat = (sp - 64).toNat + 40 := by simp [UInt32.toNat_add]; omega
  have s214 := SerdeSeqElem.f214_first (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 64) (sp - 64 + 8) (sp - 64 + 40) de ptr ob1 ob2 bs (j0 + 1) b maxP hob1 hob2 (by omega) hlen hptr
    (by omega) (by omega) (by omega) (by omega) (by rw [hw2, hj2]; exact hb2) hb93
    iprop(stk n ((sp - 64).toNat - 272) 256 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP mlen live F ∗ tbl n de) K
    (fun p c l => iprop(⌜l = UInt32.ofNat a.val.utf8ByteSize⌝ ∗ stk n ((sp - 64).toNat - 272) 256 ∗
        vt n 1057464 idx ta (A 578) ∗ tbl n de ∗ strRes n maxP live a p c ∗ rd n de ptr bs (bs.length - r.length)))
  rw [hO8, hA40, hw2, hj2, hj3, h80,
    show (sp - 64).toNat + 40 + 4 = (sp - 64).toNat + 44 by omega] at s214
  have sp169 := spec169_of_hyp (GF := GF) cfg lim inst mi n g ta A Cg gt de ptr idx bs maxP dv K169 Cd h169 (d + 2)
    (by omega) (sp - 64) ob1 hob1 (by omega) j2 a r (by omega) mlen F live hr hdv
  rw [hK, hj3] at sp169
  ihave #Sp169 := sp169 $$ HCd
  clear sp169
  generalize hT214 : (300 + 96 * w2) * cfg.regularOpCost + K = T214 at s214
  ihave #S214 := s214 $$ [Hv F169 Sp169]
  · iframe Hv F169 Sp169
  clear s214
  rw [show (1300 + 96 * (w0 + w2 + w4)) * cfg.regularOpCost + K + R =
    100 * cfg.regularOpCost + (W0 + (150 * cfg.regularOpCost + (T214 + (60 * cfg.regularOpCost +
      ((400 + 96 * w4) * cfg.regularOpCost + (190 * cfg.regularOpCost + R)))))) by
      rw [← hW0, ← hT214]; simp only [Nat.add_mul, Nat.mul_add]; omega]
  generalize hT91 : (400 + 96 * w4) * cfg.regularOpCost = T91
  simp only [f228]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (230 * cfg.regularOpCost + (T214 + (60 * cfg.regularOpCost + (T91 + (190 * cfg.regularOpCost + R)))))
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hb0]
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.optByte_byte]
  mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep [Hd]
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j0 hj0l
    (by omega) (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (160 * cfg.regularOpCost + (T214 + (60 * cfg.regularOpCost + (T91 + (190 * cfg.regularOpCost + R)))))
  mstep; mstep; mstep [A40]
  mstep; mstep; mstep [A44]
  ihave A44 := store1 n _ 1 1 (by decide) $$ A44
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S214 using [A40 A44 Hg S16 R16 Hrd S256 Hvt Hh Ht]
  · iframe A40 A44 Hg S16 R16 Hrd S256 Hvt Hh Ht
  icases HQ with ⟨%hrs, A40, A44, Hg, S16, %p, %c, %l, %hp, W8, W12, W16, W20, %hl, S256, Hvt, Ht, Hstr, Hrd⟩
  subst hrs hl
  mcredits (100 * cfg.regularOpCost + (T91 + (190 * cfg.regularOpCost + R)))
  mstep; mstep; mstep; mstep [W8]; mstep; mstep
  mstep_taken with decide
  mstep; mstep [W12]; mstep
  mstep_taken with (simp [Numeric.bool, hp])
  ihave W16 := KeyGet.join64 n ((sp - 64).toNat + 8 + 8) c (UInt32.ofNat a.val.utf8ByteSize) $$ [W16 W20]
  · rw [show (sp - 64).toNat + 8 + 8 + 4 = (sp - 64).toNat + 8 + 12 by omega]; iframe W16 W20
  mstep; mstep; mstep
  mstep [W16] with (simp [UInt32.toNat_add]; omega)
  rw [VecFromElem.ofNat_decode_pair]
  mstep; mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  iunfold strRes at Hstr
  icases Hstr with ⟨%mlen', %F', %⟨hp', hcap, hr'⟩, Hbytes, Hblk, Hh⟩
  have s91 := SerdeEndSeq.f91_spec (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 64) de ptr idx bs j3 maxP mlen' ((p.toNat, c.toNat) :: live) F' hlen hptr (by omega) (by omega) (by omega) hr'
  rw [cost91_ok cfg F' bs j3 (by rw [hw4]; exact hb4), hw4, hT91] at s91
  ihave #S91 := s91 $$ Hv
  clear s91
  ihave S16 := stk_addr (show (sp - 64).toNat - 16 = (sp - 64).toNat - 272 + 256 by omega) $$ S16
  ihave S272 := stk_join n ((sp - 64).toNat - 272) 256 16 $$ [S256 S16]
  · iframe S256 S16
  icases stk_split n ((sp - 64).toNat - 272) 160 112 $$ S272 with ⟨S160, S112⟩
  rw [show (sp - 64).toNat - 272 + 160 = (sp - 64).toNat - 112 by omega]
  mstep; mstep [Hd]; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  mstep; mstep; mstep [Hd]
  mstep
  mcall S91 using [Hg S112 Hvt Hh Hrd]
  · iframe Hg S112 Hvt Hh Hrd
  icases HQ with ⟨Hg, S112, Hvt, HQ⟩
  ihave HQ := resSeq_pos hb4 $$ HQ
  icases HQ with ⟨%hrs, Hh, Hrd⟩
  subst hrs
  mcredits (150 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep; mstep
  mstep [W16] with (simp [UInt32.toNat_add]; omega)
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep [X24] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep [W12] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep [W8] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep_not_taken with decide
  mstep
  mstep_not_taken with decide
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep [O4]
  mstep; mstep; mstep; mstep; mstep [O8] with (simp [UInt32.toNat_add]; omega)
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 64 + 64 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt Ht
  isplitl [S160 S112 X0 W8 W12 W16 X24 X28 A40 A44 A45 X48]
  · ihave S112 := stk_addr (show (sp - 64).toNat - 112 = (sp - 64).toNat - 272 + 160 by omega) $$ S112
    ihave S272 := stk_join n ((sp - 64).toNat - 272) 160 112 $$ [S160 S112]
    · iframe S160 S112
    ihave W8 := stk_word $$ W8
    ihave W12 := stk_word $$ W12
    ihave W16 := stk_intro $$ W16
    ihave X24 := stk_word $$ X24
    ihave A40 := stk_word $$ A40
    ihave A44 := stk_intro $$ A44
    ihave A45 := stk_intro $$ A45
    rw [show (bytes32 c ++ bytes32 (UInt32.ofNat a.val.utf8ByteSize)).length = 8 by simp,
      show (List.drop 1 (List.drop 4 ba)).length = 3 by simp; omega,
      show ([0] : List UInt8).length = 1 by rfl,
      show (sp - 64).toNat + 8 + 8 = (sp - 64).toNat + 16 by omega,
      show (sp - 64).toNat + 8 + 4 = (sp - 64).toNat + 12 by omega,
      show (sp - 64).toNat + 24 + 4 = (sp - 64).toNat + 28 by omega,
      show (sp - 64).toNat + 44 + 1 = (sp - 64).toNat + 45 by omega]
    ihave F64 := frame64 n (sp - 64).toNat $$ [X0 W8 W12 W16 X24 X28 A40 A44 A45 X48]
    · iframe X0 W8 W12 W16 X24 X28 A40 A44 A45 X48
    ihave F64 := stk_addr (show (sp - 64).toNat = (sp - 64).toNat - 272 + 272 by omega) $$ F64
    iapply stk_join n ((sp - 64).toNat - 272) 272 64
    iframe S272 F64
  isplitl [Hd]
  · iapply (store1 n _ _ 128 depth_back)
    iexact Hd
  iexists p
  iexists c
  ihave O8 := KeyGet.split64 n (out.toNat + 8) c (UInt32.ofNat a.val.utf8ByteSize) $$ O8
  icases O8 with ⟨O8, O12⟩
  rw [show out.toNat + 8 + 4 = out.toNat + 12 by omega]
  iframe O0 O4 O8 O12 Hrd
  iunfold strRes
  iexists mlen'
  iexists F'
  iframe Hbytes Hblk Hh
  ipureintro; exact ⟨hp', hcap, hr'⟩

end L228

end WNear.Binary.SerdeStructArr
