import Bridge.Functions.SerdeDeStr
import Bridge.Functions.ParseStrGrowth

/-!
# Successful string deserialization through a copied scratch result

The owned string and scratch remain distinct live allocations. The result retains
both and the parser's concrete growth endpoint; it does not assume that the heap
is unchanged by escaped input.
-/

namespace WNear.Binary.SerdeDeStrEsc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeString (heapS strCode cost618 costA)
open WNear.Binary.ParseStr (escTable plain ok646 cost646 res646)
open WNear.Binary.FromUtf8Gen (utf8Width)

open WNear.Binary.SerdeDeStr (code380 f343_s)
open WNear.Binary.ParseStr (strRun borrowed roomRun code646)
open WNear.Binary.ParseStrSuccess (appendChunks resStrTraced)
open WNear.Binary.ScratchGrow (sbuf endState endFreeBound growthPages)
open WNear.Binary.ParseEscape (sbufR)

/-- Decoding escapes does not increase the input-byte bound, including the consumed quote. -/
theorem strRun_size (l acc bytes rest : List UInt8) (hok : strRun l acc = .ok bytes rest) :
    bytes.length + rest.length + 1 ≤ acc.length + l.length := by
  induction hn : l.length using Nat.strong_induction_on generalizing l acc bytes rest with
  | _ len ih =>
    have hs := congrArg List.length (List.takeWhile_append_dropWhile (p := plain) (l := l))
    simp only [List.length_append] at hs
    cases hd : l.dropWhile plain with
    | nil => rw [ParseStr.strRun_nil _ _ hd] at hok; cases hok
    | cons x tail =>
      have hlen : l.length = (l.takeWhile plain).length + 1 + tail.length := by
        rw [hd] at hs; simp only [List.length_cons] at hs; omega
      rw [ParseStr.strRun_cons _ _ x tail hd] at hok
      by_cases hx : x = 0x22
      · subst x
        simp only [ite_true, ParseStr.StrOut.ok.injEq] at hok
        obtain ⟨rfl, rfl⟩ := hok
        simp only [List.length_append]
        omega
      · simp only [if_neg hx] at hok
        by_cases he : x = 0x5C
        · subst x
          simp only [ite_true] at hok
          cases hec : ParseEscape.escDecode tail with
          | none => simp [hec] at hok
          | some pr =>
            obtain ⟨eo, m⟩ := pr
            simp only [hec] at hok
            have heo := ParseStr.escDecode_len tail eo m hec
            have hlt : (tail.drop m).length < len := by simp only [List.length_drop]; omega
            have hr := ih (tail.drop m).length hlt (tail.drop m) (acc ++ l.takeWhile plain ++ eo) bytes rest hok rfl
            simp only [List.length_append, List.length_drop] at hr
            omega
        · simp [he] at hok

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Read the actual memory alignment and positivity from the allocator invariant. -/
theorem heapInv_alignment (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) :
    heapInv (GF := GF) n maxP hl live F ⊢
      ⌜hl % 65536 = 0 ∧ 0 < hl⌝ ∗ heapInv n maxP hl live F := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%M, %⟨hw, hlen⟩, Hhead, Hlen, Hmax, Hcells⟩
  isplitr
  · ipureintro
    constructor
    · simpa only [hlen] using hw.len_al
    · have hp := hw.mem0_pos
      have hb := hw.mem0_le
      omega
  iunfold heapInv
  iexists M
  iframe Hhead Hlen Hmax Hcells
  ipureintro
  exact ⟨hw, hlen⟩

/-- Room at an upper bound suffices for every smaller aligned positive memory length. -/
theorem roomFor_le (hl upper maxP : Nat) (size : UInt32) (ha : hl % 65536 = 0)
    (hp : 0 < hl) (hb : hl ≤ upper) (hr : roomFor upper maxP size) : roomFor hl maxP size := by
  unfold roomFor at hr ⊢
  refine ⟨ha, hp, by omega, ?_⟩
  exact (Nat.div_le_div_right (Nat.add_le_add_right hb _)).trans hr.2.2.2

/-- The copied scratch and the independently owned deserialized string. -/
def copiedResult (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat)
    (out de ptr capS : UInt32) (bs bytes rest : List UInt8) (q : Nat) : IProp GF :=
  iprop(∃ (scratch cap p : UInt32) (hl' F' : Nat),
    ⌜hl ≤ hl' ∧ cap = (endState capS 0 (appendChunks (bs.drop q) [])).1 ∧
      F' = endFreeBound F capS 0 (appendChunks (bs.drop q) []) ∧
      hl' ≤ hl + growthPages capS 0 (appendChunks (bs.drop q) []) * 65536⌝ ∗
    n ↦[i32][ de.toNat + 12 ] scratch ∗ n ↦[i32][ de.toNat + 16 ] cap ∗
    n ↦[i32][ de.toNat + 20 ] UInt32.ofNat bytes.length ∗ sbufR n scratch cap bytes ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
    n ↦[i32][ out.toNat + 8 ] UInt32.ofNat bytes.length ∗
    n ↦[i32][ out.toNat + 12 ] UInt32.ofNat bytes.length ∗
    heapS n maxP hl' (if cap = 0 then live else (scratch.toNat, cap.toNat) :: live) F'
      (UInt32.ofNat bytes.length) p ∗ n ↦[wms][ p.toNat ] bytes ∗
    rd n de ptr bs (bs.length - rest.length))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- `deserialize_str` accepts a valid copied string, preserving its grown scratch allocation. -/
theorem f380_copied (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 31 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx sl ptrS capS : UInt32) (ob bs bytes rest : List UInt8) (i j : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 240 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i)) (hjl' : j < bs.length)
    (hq : bs[j]? = some 0x22) (hcapS : capS.toNat < 2 ^ 25)
    (hok : strRun (bs.drop (j + 1)) [] = .ok bytes rest)
    (hutf : Utf8.utf8Ok bytes = true) (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hroom : roomRun maxP mlen capS [] (bs.drop (j + 1)))
    (halloc : roomFor (mlen + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat bytes.length)) :
    code380 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f380 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 240) 240 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
          n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
          sbuf n maxP mlen live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => (350 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost +
          (ParseStrSuccess.costRun cfg F capS [] (bs.drop (j + 1)) bs.length + 100 * cfg.regularOpCost) +
          (60 * cfg.regularOpCost + cost618 cfg
            (endFreeBound F capS 0 (appendChunks (bs.drop (j + 1)) [])) (UInt32.ofNat bytes.length)))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 240) 240 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          copiedResult n maxP mlen live F out de ptr capS bs bytes rest (j + 1))) := by
  have hsize := strRun_size (bs.drop (j + 1)) [] bytes rest hok
  have hbytes : bytes.length < 2 ^ 24 := by
    simp only [List.length_nil, Nat.zero_add, List.length_drop] at hsize
    omega
  iintro ⟨#Hv, #H646code⟩
  ihave #Hv' := Hv
  iunfold code380 at Hv'
  icases Hv' with ⟨#Hcode, #Hstr, #F927, #F657, #F647, #F648, #F646, #F640, #F322, #F332, #F333, #F339, #F674,
    #F343, #F633⟩
  ihave #Hcode' := Hcode
  iunfold errCode at Hcode'
  icases Hcode' with ⟨#H310c, -, -, -, -, -, -, -, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha339 := hm.funcs 339 (by decide)
  have ha322 := hm.funcs 322 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have ha343 := hm.funcs 343 (by decide)
  have ha646 := hm.funcs 646 (by decide)
  have ha633 := hm.funcs 633 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t13 : types[13]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hjl : j ≤ bs.length := by have := SerdeRead.wsLen_le (bs.drop i); simp at this; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Ho, Hrd, Hsl, S0, S4, Hsb, He, Hw, Ht⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  simp only [f380]
  generalize hw : wsLen (bs.drop i) = w at hj
  generalize hX1 : ParseStrSuccess.costRun cfg F capS [] (bs.drop (j + 1)) bs.length + 100 * cfg.regularOpCost = X1
  generalize hX2 : 60 * cfg.regularOpCost + cost618 cfg
    (endFreeBound F capS 0 (appendChunks (bs.drop (j + 1)) [])) (UInt32.ofNat bytes.length) = X2
  rw [show (350 + 96 * w) * cfg.regularOpCost + X1 + X2 + R =
    250 * cfg.regularOpCost + ((100 + 96 * w) * cfg.regularOpCost + (X1 + (X2 + R))) by simp only [Nat.add_mul]; omega]
  generalize hW : (100 + 96 * w) * cfg.regularOpCost = W
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep
  have key := SerdeRead.f339_spec (GF := GF) cfg lim (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi (by omega) (by omega) (by omega)
  rw [hw, ← hj, hW] at key
  mcall key using [Hrd]
  · iframe Hrd
  clear key
  mcredits (230 * cfg.regularOpCost + (X1 + (X2 + R)))
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok1 : Numeric.bool (optByte bs[j]? &&& 1 == 0) = 1 := by simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep; mstep
  icases stk_split n (sp.toNat - 240) 192 48 $$ Hs with ⟨S192, S48⟩
  rw [show sp.toNat - 240 + 192 = (sp - 48).toNat by omega]
  icases stk_split n (sp - 48).toNat 8 40 $$ S48 with ⟨F0, S40⟩
  icases stk_split n ((sp - 48).toNat + 8) 16 24 $$ S40 with ⟨A16, S24⟩
  icases stk_split n ((sp - 48).toNat + 8 + 16) 16 8 $$ S24 with ⟨B16, F8⟩
  have hB : (sp - 48 + 24).toNat = (sp - 48).toNat + 8 + 16 := by rw [UInt32.toNat_add, h48]; simp; omega
  have hA : (sp - 48 + 8).toNat = (sp - 48).toNat + 8 := by rw [UInt32.toNat_add, h48]; simp; omega
  rw [hq]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs j hjl' (by omega)
    (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hde12 : (de + 12).toNat = de.toNat + 12 := by rw [UInt32.toNat_add]; simp; omega
  ihave Hsl : n ↦[i32][ (de + 12).toNat + 8 ] sl $$ [Hsl]
  · rw [hde12, show de.toNat + 12 + 8 = de.toNat + 20 by omega]; iexact Hsl
  mstep; mstep; mstep; mstep
  mcall (f343_s cfg lim (d + 1) types[0]! (by rfl) inst mi A n g ta hm (by omega) Cg (de + 12) sl (by omega))
    using [Hsl]
  · iframe Hsl
  icases HQ with ⟨%hrs, Hsl⟩
  subst hrs
  mcredits (140 * cfg.regularOpCost + (X1 + (X2 + R)))
  iunfold stk at B16
  icases B16 with ⟨%b16, %hb16, B16⟩
  ihave B16 := memBytes_addr (show (sp - 48).toNat + 8 + 16 = (sp - 48 + 24).toNat by omega) $$ B16
  ihave S192 := stk_addr (show sp.toNat - 240 = (sp - 48).toNat - 192 by omega) $$ S192
  mstep; mstep; mstep; mstep; mstep
  ihave S0 := memBytes_addr (show de.toNat + 12 = (de + 12).toNat by omega) $$ S0
  ihave S4 := memBytes_addr (show de.toNat + 16 = (de + 12).toNat + 4 by omega) $$ S4
  have key := ParseStrSuccess.f646_success_traced (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 48) (sp - 48 + 24) de (de + 12) ptr idx ptrS capS b16 bs (j + 1)
    maxP mlen live F hb16 (by omega) hlen hptr (by omega) (by omega) (by omega) (by omega)
    hcapS hroom bytes rest hok hutf
  rw [hX1] at key
  mcall key using [Hg S192 Hvt B16 Hrd S0 S4 Hsl Hsb He Hw Ht]
  · iframe Hg S192 Hvt B16 Hrd S0 S4 Hsl Hsb He Hw Ht
  clear key
  mcredits (100 * cfg.regularOpCost + (X2 + R))
  icases HQ with ⟨%hrs, Hg, S192, Hvt, He, Hw, Ht, H646⟩
  subst hrs
  iunfold resStrTraced at H646
  simp only [hok, if_pos hutf, if_neg hcopied]
  icases H646 with ⟨Q0, Hrd, Q12, %scratch, %cap, %hl', %F', %htrace, Q4, Q8, S0, S4, Hsl, Hsb⟩
  have hF := htrace.2.2.1
  have h24 : (sp - 48 + 24).toNat = (sp - 48).toNat + 24 := by rw [UInt32.toNat_add, h48]; simp; omega
  rw [h24]
  have hm32 : (UInt32.ofNat bytes.length).toNat = bytes.length := by simp; omega
  mstep; mstep [Q4] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep; mstep [Q0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep [Q12] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep
  mstep [Q8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  iunfold sbuf at Hsb
  icases Hsb with ⟨%hbuf, Bbody, Hj, Hh⟩
  iunfold stk at A16
  icases A16 with ⟨%a16, %ha16, A16⟩
  ihave A16 := memBytes_addr (show (sp - 48).toNat + 8 = (sp - 48 + 8).toNat by omega) $$ A16
  icases stk_split n ((sp - 48).toNat - 192) 96 96 $$ S192 with ⟨S64, S96⟩
  ihave S96 := stk_addr (show (sp - 48).toNat - 192 + 96 = (sp - 48).toNat - 96 by omega) $$ S96
  mstep; mstep; mstep; mstep; mstep
  ihave Hh := heapInv_alignment n maxP hl' _ F' $$ Hh
  icases Hh with ⟨%halign, Hh⟩
  have hrOwned := roomFor_le hl' _ maxP (UInt32.ofNat bytes.length) halign.1 halign.2 htrace.2.2.2 halloc
  have key := SerdeString.f633_s (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
    (sp - 48) (sp - 48 + 8) scratch (UInt32.ofNat bytes.length) idx maxP hl'
    (if cap = 0 then live else (scratch.toNat, cap.toNat) :: live) F' a16 bytes
    ha16 (by omega) (by omega) hm32.symm (by rw [hm32]; omega) (by rw [hm32]; omega)
    (fun _ => hrOwned)
  have hX2' : 60 * cfg.regularOpCost + cost618 cfg F' (UInt32.ofNat bytes.length) = X2 := by
    rw [hF]; exact hX2
  rw [hX2'] at key
  mcall key using [Hg S96 Hvt Hh A16 Bbody]
  · iframe Hg S96 Hvt Hh A16 Bbody
  clear key
  mcredits (40 * cfg.regularOpCost + R)
  icases HQ with ⟨%hrs, %p, Hg, S96, Hvt, P0, P4, P8, P12, HA, Hp, Bbody⟩
  subst hrs
  mstep
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O12⟩
  mstep; mstep [P0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep_taken with decide
  ihave P48 := KeyGet.join64 n ((sp - 48 + 8).toNat + 4) p (UInt32.ofNat bytes.length) $$ [P4 P8]
  · rw [show (sp - 48 + 8).toNat + 4 + 4 = (sp - 48 + 8).toNat + 8 by omega]; iframe P4 P8
  mstep; mstep
  mstep [P48] with (simp [UInt32.toNat_add]; omega)
  rw [ofNat_decode_pair]
  mstep [O4]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [P12] with (simp [UInt32.toNat_add]; omega)
  mstep [O12] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep; mstep; mstep [O0]
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 48 + 48 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hg Hvt He Hw Ht
  isplitr [S0 S4 Hsl Hj HA Hp O0 O4 O12 Hrd Bbody]
  · ihave P0 := stk_word n _ _ $$ P0
    ihave P48 := stk_intro n _ _ $$ P48
    ihave P12 := stk_word n _ _ $$ P12
    rw [show (bytes32 p ++ bytes32 (UInt32.ofNat bytes.length)).length = 8 by simp]
    ihave A4 := stk_join n (sp - 48 + 8).toNat 4 8 $$ [P0 P48]
    · iframe P0 P48
    ihave A16 := stk_join n (sp - 48 + 8).toNat 12 4 $$ [A4 P12]
    · rw [show (sp - 48 + 8).toNat + 12 = (sp - 48 + 8).toNat + 12 by rfl]; iframe A4 P12
    ihave A16 := stk_addr (show (sp - 48 + 8).toNat = (sp - 48).toNat + 8 by omega) $$ A16
    ihave Q0 := stk_word n _ _ $$ Q0
    ihave Q4 := stk_word n _ _ $$ Q4
    ihave Q8 := stk_word n _ _ $$ Q8
    ihave Q12 := stk_word n _ _ $$ Q12
    ihave B16 := VecFromElem.stk16_join n ((sp - 48).toNat + 24) $$ [Q0 Q4 Q8 Q12]
    · iframe Q0 Q4 Q8 Q12
    ihave B16 := stk_addr (show (sp - 48).toNat + 24 = (sp - 48).toNat + 8 + 16 by omega) $$ B16
    ihave S24 := stk_join n ((sp - 48).toNat + 8 + 16) 16 8 $$ [B16 F8]
    · iframe B16 F8
    ihave S40 := stk_join n ((sp - 48).toNat + 8) 16 24 $$ [A16 S24]
    · iframe A16 S24
    ihave S48 := stk_join n (sp - 48).toNat 8 40 $$ [F0 S40]
    · iframe F0 S40
    ihave S96 := stk_addr (show (sp - 48).toNat - 96 = (sp - 48).toNat - 192 + 96 by omega) $$ S96
    ihave S192 := stk_join n ((sp - 48).toNat - 192) 96 96 $$ [S64 S96]
    · iframe S64 S96
    ihave S192 := stk_addr (show (sp - 48).toNat - 192 = sp.toNat - 240 by omega) $$ S192
    ihave S48 := stk_addr (show (sp - 48).toNat = sp.toNat - 240 + 192 by omega) $$ S48
    iapply stk_join n (sp.toNat - 240) 192 48
    iframe S192 S48
  iunfold copiedResult
  iexists scratch, cap, p, hl', F'
  isplitr
  · ipureintro; exact htrace
  ihave O4 := KeyGet.split64 n (out.toNat + 4) p (UInt32.ofNat bytes.length) $$ O4
  icases O4 with ⟨O4, O8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega, show out.toNat + 4 + 8 = out.toNat + 12 by omega]
  ihave S0 := memBytes_addr (show (de + 12).toNat = de.toNat + 12 by omega) $$ S0
  ihave S4 := memBytes_addr (show (de + 12).toNat + 4 = de.toNat + 16 by omega) $$ S4
  ihave Hsl := memBytes_addr (show (de + 12).toNat + 8 = de.toNat + 20 by omega) $$ Hsl
  iframe S0 S4 Hsl O0 O4 O8 O12 Hp Hrd
  isplitl [Bbody Hj]
  · iunfold sbufR
    iframe Bbody Hj
    ipureintro; exact hbuf
  iexact HA

/-- Successful copied deserialization: linear instruction work, scratch growth and the owned copy. -/
def costCopied (cfg : WasmConfig) (F : Nat) (capS : UInt32) (bs bytes rest : List UInt8) (i j : Nat) : Nat :=
  (910 + 96 * wsLen (bs.drop i) +
            470 * ((bs.drop (j + 1)).length - rest.length)) * cfg.regularOpCost +
          ParseStrSuccess.growthBudget cfg F
            (ScratchGrow.growthCount capS 0 (appendChunks (bs.drop (j + 1)) [])) bytes.length +
          cost618 cfg (endFreeBound F capS 0 (appendChunks (bs.drop (j + 1)) [])) (UInt32.ofNat bytes.length)

/-- Copied string deserialization with linear instruction work and explicit amortized growth charges. -/
theorem f380_copied_growth (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 31 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx sl ptrS capS : UInt32) (ob bs bytes rest : List UInt8) (i j : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 240 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i)) (hjl' : j < bs.length)
    (hq : bs[j]? = some 0x22) (hcapS : capS.toNat < 2 ^ 25)
    (hok : strRun (bs.drop (j + 1)) [] = .ok bytes rest)
    (hutf : Utf8.utf8Ok bytes = true) (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hroom : roomRun maxP mlen capS [] (bs.drop (j + 1)))
    (halloc : roomFor (mlen + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat bytes.length)) :
    code380 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f380 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 240) 240 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
          n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
          sbuf n maxP mlen live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => costCopied cfg F capS bs bytes rest i j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 240) 240 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          copiedResult n maxP mlen live F out de ptr capS bs bytes rest (j + 1))) := by
  apply (f380_copied cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx sl ptrS capS ob bs bytes rest i j maxP mlen live F hob hout hlen hptr hde hsp
    hi hj hjl' hq hcapS hok hutf hcopied hroom halloc).trans
  apply AllocGen.MFunSpec_cost
  intro args
  unfold costCopied
  have hsmall : ([] : List UInt8).length + (bs.drop (j + 1)).length < 2 ^ 27 := by simp; omega
  have hb := (ParseStrSuccess.costRun_growth cfg F capS [] (bs.drop (j + 1)) bytes rest bs.length hok hsmall).2
  have hg := ParseStrSuccess.appendChunks_growthBudget cfg F capS [] (bs.drop (j + 1)) bytes rest
    hok (by simp) (by omega) hsmall
  simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl, Nat.mul_zero, Nat.add_zero] at hb hg
  simp only [Nat.add_mul] at hb ⊢
  omega

end Proof
end WNear.Binary.SerdeDeStrEsc
