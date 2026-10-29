import Bridge.Functions.SerdeAccountId
import Bridge.Functions.SerdeDeStrEsc

/-!
# Successful escaped account-id deserialization

The owned String moves through 379 and 169 while the grown parser scratch remains
live in the same allocator invariant. These contracts retain both allocations.
-/

namespace WNear.Binary.SerdeAccountIdEsc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeString (heapS heapS_bound cost618)
open WNear.Binary.ParseStr (escTable plain ok646 cost646)
open WNear.Binary.FromUtf8Gen (utf8Width)
open WNear.Binary.SerdeDeStr (code380 ok380 res380 cost380 f380_s)
open WNear.Binary.AccountIdValid (cost554 f554_spec)

open WNear.Binary.SerdeDeStrEsc (copiedResult costCopied)
open WNear.Binary.SerdeAccountId (code169 f501_valid)
open WNear.Binary.ParseStr (strRun borrowed roomRun code646)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (sbuf growthPages)

/-- A string accepted by the JSON model supplies the exact bytes and UTF-8 premise of 646. -/
theorem strRun_of_stringBody (l : List UInt8) (s : String) (rest : List UInt8)
    (hs : NearInterface.Json.stringBody l [] = some (some s, rest)) :
    strRun l [] = .ok s.toUTF8.toList rest ∧ Utf8.utf8Ok s.toUTF8.toList = true := by
  have hm := ParseStr.strRun_model l []
  simp only [List.reverse_nil] at hm
  rw [hs] at hm
  cases hr : strRun l [] with
  | eof | ctrl | badEsc => simp [hr] at hm
  | ok bytes r =>
    simp only [hr, Option.some.injEq, Prod.mk.injEq] at hm
    have hb := Wasm.ByteEncoding.string_fromUTF8_some_bytes ⟨bytes.toArray⟩ s hm.1.symm
    have hbl : s.toUTF8.toList = bytes := by
      simpa only [Wasm.ByteEncoding.byteArray_toList_ofArray, List.toList_toArray] using congrArg ByteArray.toList hb
    have hu := Utf8.fromUTF8?_isSome bytes
    rw [hm.1.symm] at hu
    simp only [Option.isSome_some] at hu
    rw [← hbl] at hr hu
    exact ⟨by rw [← hbl, hm.2], hu.symm⟩

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- The String deserialization wrapper preserves the copied parser result. -/
theorem f379_copied (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 32 < lim.maxCallDepth) (Cg : Nat)
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
    code380 n maxP inst mi A ∗ code646 n maxP inst mi A ∗ A 380 ↪[wf] FuncInst.wasm types[14]! inst f380 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f379 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 240) 240 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
          n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
          sbuf n maxP mlen live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => 30 * cfg.regularOpCost + costCopied cfg F capS bs bytes rest i j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 240) 240 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          copiedResult n maxP mlen live F out de ptr capS bs bytes rest (j + 1))) := by
  iintro ⟨#Hv, #H646, #F380⟩
  ihave #Hv' := Hv
  iunfold code380 at Hv'
  icases Hv' with ⟨#Hcode, -⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have ha380 := hm.funcs 380 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Ho, Hrd, Hsl, S0, S4, Hsb, He, Hw, Ht⟩
  subst hargs
  simp only [f379]
  have key := SerdeDeStrEsc.f380_copied_growth (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm
    (by omega) Cg gt sp out de ptr idx sl ptrS capS ob bs bytes rest i j maxP mlen live F
    hob hout hlen hptr hde hsp hi hj hjl' hq hcapS hok hutf hcopied hroom halloc
  generalize hK : costCopied cfg F capS bs bytes rest i j = K at key ⊢
  rw [show 30 * cfg.regularOpCost + K + R = 30 * cfg.regularOpCost + (K + R) by omega]
  mstep; mstep
  mcall key using [Hg Hs Hvt Ho Hrd Hsl S0 S4 Hsb He Hw Ht]
  · iframe Hg Hs Hvt Ho Hrd Hsl S0 S4 Hsb He Hw Ht
  clear key
  icases HQ with ⟨%hrs, Hg, Hs, Hvt, He, Hw, Ht, Hres⟩
  subst hrs
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hs Hvt He Hw Ht Hres
  ipureintro; simp [htype]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Valid copied account ids move into the output, preserving the parser scratch and heap state. -/
theorem f169_copied (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 33 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx sl ptrS capS : UInt32) (ob bs bytes rest : List UInt8) (i j : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 288 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i)) (hjl' : j < bs.length)
    (hq : bs[j]? = some 0x22) (hcapS : capS.toNat < 2 ^ 25)
    (hok : strRun (bs.drop (j + 1)) [] = .ok bytes rest)
    (hutf : Utf8.utf8Ok bytes = true) (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hroom : roomRun maxP mlen capS [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes bytes = true)
    (halloc : roomFor (mlen + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat bytes.length)) :
    code169 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f169 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 288) 288 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
          n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
          sbuf n maxP mlen live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => (400 + cost554 bytes.length) * cfg.regularOpCost + costCopied cfg F capS bs bytes rest i j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 288) 288 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          copiedResult n maxP mlen live F out de ptr capS bs bytes rest (j + 1))) := by
  iintro ⟨#Hv, #H646⟩
  ihave #Hv' := Hv
  iunfold code169 at Hv'
  icases Hv' with ⟨#H380c, #F380, #F379, #F617, #F501, #F502, #F554, #F673, #F779⟩
  ihave #Hc380 := H380c
  iunfold code380 at Hc380
  icases Hc380 with ⟨#Hcode, -⟩
  iunfold errCode at Hcode
  icases Hcode with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha379 := hm.funcs 379 (by decide)
  have ha617 := hm.funcs 617 (by decide)
  have ha501 := hm.funcs 501 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  have t32r : types[32]!.results.length = 1 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Ho, Hrd, Hsl, S0, S4, Hsb, He, Hw, Ht⟩
  subst hargs
  have hlt := sp.toNat_lt
  have h48 : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hA : (sp - 48 + 8).toNat = (sp - 48).toNat + 8 := by rw [UInt32.toNat_add, h48]; simp; omega
  have hB : (sp - 48 + 32).toNat = (sp - 48).toNat + 32 := by rw [UInt32.toNat_add, h48]; simp; omega
  icases stk_split n (sp.toNat - 288) 240 48 $$ Hs with ⟨S240, S48⟩
  rw [show sp.toNat - 288 + 240 = (sp - 48).toNat by omega]
  icases stk_split n (sp - 48).toNat 8 40 $$ S48 with ⟨F0, S40⟩
  icases stk_split n ((sp - 48).toNat + 8) 16 24 $$ S40 with ⟨A16, S24⟩
  icases stk_split n ((sp - 48).toNat + 8 + 16) 8 16 $$ S24 with ⟨G8, S16⟩
  icases stk_split n ((sp - 48).toNat + 8 + 16 + 8) 12 4 $$ S16 with ⟨B12, Z4⟩
  iunfold stk at A16 B12
  icases A16 with ⟨%a16, %ha16, A16⟩
  icases B12 with ⟨%b12, %hb12, B12⟩
  ihave A16 := memBytes_addr (show (sp - 48).toNat + 8 = (sp - 48 + 8).toNat by omega) $$ A16
  ihave S240 := stk_addr (show sp.toNat - 288 = (sp - 48).toNat - 240 by omega) $$ S240
  simp only [f169]
  generalize hK : costCopied cfg F capS bs bytes rest i j = K
  rw [show (400 + cost554 bytes.length) * cfg.regularOpCost + K + R =
    210 * cfg.regularOpCost + ((30 * cfg.regularOpCost + K) + ((160 + cost554 bytes.length) * cfg.regularOpCost + R)) by
      simp only [Nat.add_mul]; omega]
  generalize hV : (160 + cost554 bytes.length) * cfg.regularOpCost = V
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  have key := f379_copied (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm
    (by omega) Cg gt (sp - 48) (sp - 48 + 8) de ptr idx sl ptrS capS a16 bs bytes rest i j
    maxP mlen live F ha16 (by omega) hlen hptr hde (by omega) hi hj hjl' hq hcapS hok hutf hcopied hroom halloc
  rw [hK] at key
  mcall key using [Hg S240 Hvt A16 Hrd Hsl S0 S4 Hsb He Hw Ht]
  · iframe Hg S240 Hvt A16 Hrd Hsl S0 S4 Hsb He Hw Ht
  clear key
  icases HQ with ⟨%hrs, Hg, S240, Hvt, He, Hw, Ht, Hres⟩
  subst hrs
  mcredits (150 * cfg.regularOpCost + (V + R))
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O12⟩
  iunfold copiedResult at Hres
  icases Hres with ⟨%scratch, %cap, %p, %hl', %F', %htrace, S0, S4, Hsl, Hscratch, Q0, Q4, Q8, Q12, HS, Hp, Hrd⟩
  rw [hA]
  ihave HS := heapS_bound $$ HS
  icases HS with ⟨%hpb, HS⟩
  have hsize := SerdeDeStrEsc.strRun_size (bs.drop (j + 1)) [] bytes rest hok
  have hm28 : bytes.length < 2 ^ 28 := by
    simp only [List.length_nil, Nat.zero_add, List.length_drop] at hsize
    omega
  have hm32 : (UInt32.ofNat bytes.length).toNat = bytes.length := by simp; omega
  rw [hm32] at hpb
  generalize hmm : UInt32.ofNat bytes.length = m at *
  mstep; mstep [Q4] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep; mstep
  mstep; mstep [Q0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep_not_taken with decide
  ihave Q812 := KeyGet.join64 n ((sp - 48).toNat + 8 + 8) m m $$ [Q8 Q12]
  · rw [show (sp - 48).toNat + 8 + 8 + 4 = (sp - 48).toNat + 8 + 12 by omega,
      show (sp - 48).toNat + 8 + 8 = (sp - 48).toNat + 8 + 8 by rfl]
    iframe Q8 Q12
  icases U128From.memBytes_split n ((sp - 48).toNat + 8 + 16 + 8) 4 b12 (by omega) $$ B12 with ⟨B0, B4⟩
  mstep; mstep; mstep; mstep
  mstep [Q812] with (simp [UInt32.toNat_add]; omega)
  rw [ofNat_decode_pair]
  mstep [B4] with (simp [UInt32.toNat_add]; omega)
  rw [storeBytes_pair64]
  mstep; mstep
  mstep [B0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep; mstep; mstep; mstep
  ihave B4 := KeyGet.split64 n ((sp - 48).toNat + 8 + 16 + 8 + 4) m m $$ B4
  icases B4 with ⟨B4, B8⟩
  ihave Q812 := KeyGet.split64 n ((sp - 48).toNat + 8 + 8) m m $$ Q812
  icases Q812 with ⟨Q8, Q12⟩
  ihave J1 := KeyGet.join64 n ((sp - 48).toNat + 8) 0 p $$ [Q0 Q4]
  · iframe Q0 Q4
  ihave J2 := KeyGet.join64 n ((sp - 48).toNat + 8 + 8) m m $$ [Q8 Q12]
  · rw [show (sp - 48).toNat + 8 + 8 + 4 = (sp - 48).toNat + 8 + 12 by omega]; iframe Q8 Q12
  ihave J := U128From.memBytes_join n ((sp - 48).toNat + 8) 8 (bytes32 0 ++ bytes32 p) (bytes32 m ++ bytes32 m)
    (by simp) $$ [J1 J2]
  · iframe J1 J2
  ihave J := memBytes_addr (show (sp - 48).toNat + 8 = (sp - 48 + 8).toNat by omega) $$ J
  icases stk_split n ((sp - 48).toNat - 240) 176 64 $$ S240 with ⟨S176, S64⟩
  ihave S64 := stk_addr (show (sp - 48).toNat - 240 + 176 = (sp - 48).toNat - 64 by omega) $$ S64
  ihave B0 : n ↦[i32][ (sp - 48 + 32).toNat ] p $$ [B0]
  · rw [hB, show (sp - 48).toNat + 32 = (sp - 48).toNat + 8 + 16 + 8 by omega]; iexact B0
  ihave B4 : n ↦[i32][ (sp - 48 + 32).toNat + 4 ] m $$ [B4]
  · rw [hB, show (sp - 48).toNat + 32 + 4 = (sp - 48).toNat + 8 + 16 + 8 + 4 by omega]; iexact B4
  ihave B8 : n ↦[i32][ (sp - 48 + 32).toNat + 8 ] m $$ [B8]
  · rw [hB, show (sp - 48).toNat + 32 + 8 = (sp - 48).toNat + 8 + 16 + 8 + 4 + 4 by omega]; iexact B8
  have key := f501_valid (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg (A 673) (A 554) (A 779)
    (A 502) (hm.funcs 673 (by decide)) (hm.funcs 554 (by decide)) (hm.funcs 779 (by decide))
    (hm.funcs 502 (by decide)) (by omega) Cg gt (sp - 48) (sp - 48 + 8) (sp - 48 + 32) p m m
    (bytes32 0 ++ bytes32 p ++ (bytes32 m ++ bytes32 m)) bytes (by simp) (by omega) (by omega)
    hm32.symm (by omega) (by omega) hvalid
  rw [hm32, hV] at key
  mcall key using [Hg S64 J B0 B4 B8 Hp]
  · iframe Hg S64 J B0 B4 B8 Hp
  clear key
  icases HQ with ⟨%hrs, Hg, S64, R0, R4, R8, R12, B0, B4, B8, Hp⟩
  subst hrs
  mcredits (70 * cfg.regularOpCost + R)
  rw [hA]
  mstep; mstep
  mstep; mstep [R0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep_taken with decide
  ihave R48 := KeyGet.join64 n ((sp - 48).toNat + 8 + 4) p m $$ [R4 R8]
  · rw [show (sp - 48).toNat + 8 + 4 + 4 = (sp - 48).toNat + 8 + 8 by omega]; iframe R4 R8
  mstep; mstep
  mstep [R48] with (simp [UInt32.toNat_add]; omega)
  rw [ofNat_decode_pair]
  mstep [O4]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [R12] with (simp [UInt32.toNat_add]; omega)
  mstep [O12] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep; mstep; mstep [O0]
  mstep
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
  isplitr [S0 S4 Hsl Hscratch HS Hp O0 O4 O12 Hrd]
  · ihave R0 := stk_word n _ _ $$ R0
    ihave R48 := stk_intro n _ _ $$ R48
    ihave R12 := stk_word n _ _ $$ R12
    rw [show (bytes32 p ++ bytes32 m).length = 8 by simp]
    ihave A := stk_join n ((sp - 48).toNat + 8) 4 8 $$ [R0 R48]
    · iframe R0 R48
    ihave A := stk_join n ((sp - 48).toNat + 8) 12 4 $$ [A R12]
    · rw [show (sp - 48).toNat + 8 + 12 = (sp - 48).toNat + 8 + 12 by rfl]; iframe A R12
    ihave B0 := stk_word n _ _ $$ B0
    ihave B4 := stk_word n _ _ $$ B4
    ihave B8 := stk_word n _ _ $$ B8
    ihave Bj := stk_join n ((sp - 48 + 32).toNat + 4) 4 4 $$ [B4 B8]
    · rw [show (sp - 48 + 32).toNat + 4 + 4 = (sp - 48 + 32).toNat + 8 by omega]; iframe B4 B8
    ihave Bj := stk_join n (sp - 48 + 32).toNat 4 8 $$ [B0 Bj]
    · iframe B0 Bj
    ihave Bj := stk_addr (show (sp - 48 + 32).toNat = (sp - 48).toNat + 8 + 16 + 8 by omega) $$ Bj
    ihave S := stk_join n ((sp - 48).toNat + 8 + 16 + 8) 12 4 $$ [Bj Z4]
    · iframe Bj Z4
    ihave S := stk_join n ((sp - 48).toNat + 8 + 16) 8 16 $$ [G8 S]
    · iframe G8 S
    ihave S := stk_join n ((sp - 48).toNat + 8) 16 24 $$ [A S]
    · iframe A S
    ihave S := stk_join n (sp - 48).toNat 8 40 $$ [F0 S]
    · iframe F0 S
    ihave S64 := stk_addr (show (sp - 48).toNat - 64 = (sp - 48).toNat - 240 + 176 by omega) $$ S64
    ihave S240 := stk_join n ((sp - 48).toNat - 240) 176 64 $$ [S176 S64]
    · iframe S176 S64
    ihave S240 := stk_addr (show (sp - 48).toNat - 240 = sp.toNat - 288 by omega) $$ S240
    ihave S := stk_addr (show (sp - 48).toNat = sp.toNat - 288 + 240 by omega) $$ S
    iapply stk_join n (sp.toNat - 288) 240 48
    iframe S240 S
  iunfold copiedResult
  iexists scratch, cap, p, hl', F'
  isplitr
  · ipureintro; exact htrace
  ihave O4 := KeyGet.split64 n (out.toNat + 4) p m $$ O4
  icases O4 with ⟨O4, O8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega, show out.toNat + 4 + 8 = out.toNat + 12 by omega, hmm]
  iframe S0 S4 Hsl Hscratch O0 O4 O8 O12 HS Hp Hrd

/-- The copied account-id reader stated directly against the JSON model's string decoder. -/
theorem f169_copied_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 33 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out de ptr idx sl ptrS capS : UInt32) (ob bs : List UInt8) (value : String) (rest : List UInt8) (i j : Nat)
    (maxP mlen : Nat) (live : List (Nat × Nat)) (F : Nat)
    (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32) (hlen : bs.length < 2 ^ 24)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hsp : 288 ≤ sp.toNat)
    (hi : i ≤ bs.length) (hj : j = i + wsLen (bs.drop i)) (hjl' : j < bs.length)
    (hq : bs[j]? = some 0x22) (hcapS : capS.toNat < 2 ^ 25)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest))
    (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hroom : roomRun maxP mlen capS [] (bs.drop (j + 1)))
    (hvalid : validAccountIdBytes (value.toUTF8.toList) = true)
    (halloc : roomFor (mlen + growthPages capS 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      maxP (UInt32.ofNat (value.toUTF8.toList).length)) :
    code169 n maxP inst mi A ∗ code646 n maxP inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f169 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 288) 288 ∗ vt n 1057464 idx ta (A 578) ∗
          n ↦[wms][ out.toNat ] ob ∗ rd n de ptr bs i ∗ n ↦[i32][ de.toNat + 20 ] sl ∗
          n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
          sbuf n maxP mlen live F ptrS capS [] ∗
          n ↦[wms][ 1062392 ] escTable ∗ n ↦[wms][ 1071704 ] utf8Width ∗
          n ↦[wms][ 1062712 ] SerdeEsc.hexTable))
        (fun _ => (400 + cost554 (value.toUTF8.toList).length) * cfg.regularOpCost + costCopied cfg F capS bs (value.toUTF8.toList) rest i j)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 288) 288 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1062392 ] escTable ∗
          n ↦[wms][ 1071704 ] utf8Width ∗ n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
          copiedResult n maxP mlen live F out de ptr capS bs (value.toUTF8.toList) rest (j + 1))) := by
  obtain ⟨hok, hutf⟩ := strRun_of_stringBody (bs.drop (j + 1)) value rest hmodel
  exact f169_copied cfg lim d type htype inst mi A n g ta hm hd Cg gt
    sp out de ptr idx sl ptrS capS ob bs value.toUTF8.toList rest i j maxP mlen live F
    hob hout hlen hptr hde hsp hi hj hjl' hq hcapS hok hutf hcopied hroom hvalid halloc

end Proof
end WNear.Binary.SerdeAccountIdEsc
