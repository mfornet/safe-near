import Bridge.Functions.BorshFT

/-!
# `<Contract as BorshDeserialize>::deserialize` (162) and `try_from_slice` (161)

```wat
;; 162 (out, r): sp -= 96
;;     425(sp + 48, r)                          ;; Result<FungibleToken>: tag at 48, value at 56..96
;;     w := [sp+52] (i64); tag := [sp+48]; memcpy(sp + 12, sp + 60, 36)
;;     tag = 1 → Err (not on our path)
;;     out+8 := w >> 32 (store32); memcpy(out + 12, sp + 12, 36); out := 0 (Ok)
;; 161 try_from_slice (out, ptr, len): sp -= 144; the reader (ptr, len) at sp + 8
;;     162(sp + 96, sp + 8)                     ;; tag at 96, value at 104..144
;;     w := [sp+100] (i64); tag := [sp+96]; memcpy(sp + 60, sp + 108, 36)
;;     tag = 1 → Err;  [sp+16] := w >> 32; memcpy(sp + 20, sp + 60, 36)
;;     [sp+12] ≠ 0 (bytes left) → Err "Not all bytes read"
;;     memcpy(out + 8, sp + 16, 40); out := 0 (Ok)
```

The `Contract`'s 40 bytes are the 36 of `ftHead` and 4 bytes of padding, copied from the
frames as they are (`pad`, any contents).
-/

namespace WNear.Binary.BorshContract

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.BorshLeaves WNear.Binary.BorshInt WNear.Binary.BorshVec WNear.Binary.BorshBytes
open WNear.Binary.BorshFT
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro pair64 storeBytes_pair64
  ofNat_decode_pair roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.Interface (IfaceMod)

/-- `i64.store32` of the high word of an `i64` loaded from `a ++ b` writes `b`. -/
theorem store32_hi (a b : List UInt8) (ha : a.length = 4) (hb : b.length = 4) :
    storeBytes (.i64 (UInt64.ofNat (Memory.decodeLE (a ++ b)) >>> (32 % 64))) 4 = b := by
  match a, b, ha, hb with
  | [a0, a1, a2, a3], [b0, b1, b2, b3], _, _ =>
    have h0 := a0.toNat_lt; have h1 := a1.toNat_lt; have h2 := a2.toNat_lt; have h3 := a3.toNat_lt
    have g0 := b0.toNat_lt; have g1 := b1.toNat_lt; have g2 := b2.toNat_lt; have g3 := b3.toNat_lt
    simp only [storeBytes, storeRaw, Memory.decodeLE, List.foldr, List.cons_append, List.nil_append,
      List.range, List.range.loop, List.map, Nat.shiftRight_eq_div_pow, List.cons.injEq, and_true,
      UInt64.toNat_shiftRight, UInt64.toNat_ofNat']
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply UInt8.toNat_inj.mp; simp [Nat.shiftRight_eq_div_pow] <;> omega)

theorem memcpy36 : MemCpy.cost 36 = 654 := rfl
theorem memcpy40 : MemCpy.cost 40 = 726 := rfl

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `memcpy` of 36 bytes. -/
theorem memcpy_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (dst src : UInt32) (k : Nat) (hk : k < 2 ^ 32) (hk0 : k ≠ 0)
    (ob sb : List UInt8) (hob : ob.length = k) (hsb : sb.length = k)
    (hdst : dst.toNat + k ≤ 2 ^ 32) (hsrc : src.toNat + k ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d types[15]! inst mi f951 Cg (MemCpy.pre n dst src (UInt32.ofNat k) ob sb)
        (fun _ => (18 * k + 6) * cfg.regularOpCost) (MemCpy.post n dst src sb) := by
  have hkk : (UInt32.ofNat k).toNat = k := by simp; omega
  have h := MemCpy.f951_spec (GF := GF) cfg lim d types[15]! rfl inst mi n hn Cg dst src (UInt32.ofNat k) ob sb
    (by rw [hkk]; exact hob) (by rw [hkk]; exact hsb) (by rw [hkk]; exact hdst) (by rw [hkk]; exact hsrc)
  simp only [MemCpy.cost, hkk, hk0, if_false] at h
  exact h

/-- The code `Contract::deserialize` runs (persistent). -/
def contractCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(ftCode n maxP inst mi A ∗ A 425 ↪[wf] FuncInst.wasm types[14]! inst f425 ∗
    A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗ A 162 ↪[wf] FuncInst.wasm types[14]! inst f162)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (contractCode (GF := GF) n maxP inst mi A) := by
  unfold contractCode; infer_instance

/-- The `Contract` at `a`: `ftHead` and four bytes of padding; the prefix block `p` live. -/
def contractAt (n maxP len : Nat) (live : List (Nat × Nat)) (a : Nat) (b0 b1 c0 pre : List UInt8) : IProp GF :=
  iprop(∃ (p : UInt32) (pad : List UInt8), ⌜pad.length = 4⌝ ∗ n ↦[wms][ a ] (ftHead b0 b1 c0 p pre ++ pad) ∗
    heapWith n maxP len live p pre)

def pre162 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (o0 o8 hd pre b0 b1 c0 : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 r]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 352) 352 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗ rdr n r q m ∗
    n ↦[wms][ out.toNat ] o0 ∗ n ↦[wms][ out.toNat + 8 ] o8 ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] pre ∗ n ↦[wms][ q.toNat + 4 + pre.length ] b0 ∗
    n ↦[wms][ q.toNat + 4 + pre.length + 8 ] b1 ∗ n ↦[wms][ q.toNat + 4 + pre.length + 16 ] c0)

def post162 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (hd pre b0 b1 c0 : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 352) 352 ∗ vt n 1057464 idx ta a578 ∗
    rdr n r (q + 4 + UInt32.ofNat pre.length + 16 + 8) (m - 4 - UInt32.ofNat pre.length - 16 - 8) ∗
    n ↦[i32][ out.toNat ] 0 ∗ contractAt n maxP len live (out.toNat + 8) b0 b1 c0 pre ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] pre ∗ n ↦[wms][ q.toNat + 4 + pre.length ] b0 ∗
    n ↦[wms][ q.toNat + 4 + pre.length + 8 ] b1 ∗ n ↦[wms][ q.toNat + 4 + pre.length + 16 ] c0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`<Contract as BorshDeserialize>::deserialize`** (162): 425 into the frame, `Ok` and the
`Contract` (`contractAt`) at `out`. -/
theorem f162_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o0 o8 hd4 pre b0 b1 c0 : List UInt8) (ho0 : o0.length = 4) (ho8 : o8.length = 40) (hhd : hd4.length = 4)
    (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hc0 : c0.length = 8)
    (hL : Memory.decodeLE hd4 = pre.length) (hL0 : 0 < pre.length) (hL28 : pre.length < 2 ^ 28)
    (hroom : roomFor len maxP (UInt32.ofNat pre.length))
    (hs : 352 ≤ s.toNat) (hmL : 4 + pre.length + 24 ≤ m.toNat)
    (hq : q.toNat + 4 + pre.length + 24 ≤ 2 ^ 32) (hout : out.toNat + 48 ≤ 2 ^ 32) (hr : r.toNat + 8 ≤ 2 ^ 32) :
    contractCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f162 Cg
        (pre162 n g gt s out r q m idx ta (A 578) maxP len live o0 o8 hd4 pre b0 b1 c0)
        (fun _ => 93 * cfg.regularOpCost + cost425 cfg (UInt32.ofNat pre.length) + 654 * cfg.regularOpCost +
          654 * cfg.regularOpCost)
        (post162 n g gt s out r q m idx ta (A 578) maxP len live hd4 pre b0 b1 c0) := by
  iintro #Hcode
  ihave #Hcode' := Hcode
  iunfold contractCode at Hcode'
  icases Hcode' with ⟨#Hft, #H425, #H951, -⟩
  ihave #Hft' := Hft
  iunfold ftCode, bytesCode, rdCode at Hft'
  icases Hft' with ⟨⟨⟨#Hi, -⟩, -⟩, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha425 := hm.funcs 425 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h96 : (s - 96).toNat = s.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e48 : (s - 96 + 48).toNat = s.toNat - 48 := by simp [UInt32.toNat_add, h96]; omega
  have e12 : (s - 96 + 12).toNat = s.toNat - 84 := by simp [UInt32.toNat_add, h96]; omega
  have e60 : (s - 96 + 48 + 12).toNat = s.toNat - 36 := by simp [UInt32.toNat_add, h96]; omega
  have M36 := memcpy_spec (GF := GF) cfg lim (d + 1) inst mi n hn Cg
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre162 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hr, Ho0, Ho8, Hd4, Hpre, B0, B1, C0⟩
  subst hargs
  ihave Ho8 := U128From.memBytes_split n (out.toNat + 8) 4 o8 (by omega) $$ Ho8
  icases Ho8 with ⟨Ho8, Ho12⟩
  icases stkSp 256 96 rfl $$ Hs with ⟨Lo, Hs⟩
  icases stkSp 12 84 rfl $$ Hs with ⟨F0, Hs⟩
  icases stkSp 36 48 rfl $$ Hs with ⟨F12, Hs⟩
  icases stkSp 4 44 rfl $$ Hs with ⟨F48, Hs⟩
  icases stkSp 4 40 rfl $$ Hs with ⟨F52, Hs⟩
  icases stkSp 36 4 rfl $$ Hs with ⟨F56, F92⟩
  icases stk_bytes' $$ F12 with ⟨%f12, %hf12, F12⟩
  icases stk_bytes' $$ F48 with ⟨%f48, %hf48, F48⟩
  icases stk_bytes' $$ F52 with ⟨%f52, %hf52, F52⟩
  icases stk_bytes' $$ F56 with ⟨%f56, %hf56, F56⟩
  icases stk_bytes' $$ F92 with ⟨%f92, %hf92, F92⟩
  simp only [f162]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (f425_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 96) (s - 96 + 48)
      r q m idx maxP len live f48 f56 hd4 pre b0 b1 c0 hf48 hf56 hhd hb0 hb1 hc0 hL hL0 hL28 hroom (by omega) hmL hq
      (by omega) hr)
    using [Hg Lo Hvt Hinv Hr F48 F56 Hd4 Hpre B0 B1 C0]
  · iunfold pre425
    ihave Lo := stkA (b := (s - 96).toNat - 256) (by omega) $$ Lo
    ihave F48 := memBytes_addr (a := s.toNat - 352 + 256 + 12 + 36) (b := (s - 96 + 48).toNat) (by omega) $$ F48
    ihave F56 := memBytes_addr (a := s.toNat - 352 + 256 + 12 + 36 + 4 + 4) (b := (s - 96 + 48).toNat + 8)
      (by omega) $$ F56
    iframe Hg Lo Hvt Hinv Hr F48 F56 Hd4 Hpre B0 B1 C0
    ipureintro; rfl
  iunfold post425 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hr, T48, ⟨%p, FT, HW⟩, Hd4, Hpre, B0, B1, C0⟩
  subst hrs
  have hft := ftHead_length b0 b1 c0 p pre hb0 hb1 hc0
  generalize hftd : ftHead b0 b1 c0 p pre = ft at hft ⊢
  ihave FT := memBytes_addr (a := (s - 96 + 48).toNat + 8) (b := s.toNat - 40) (by omega) $$ FT
  ihave FT := U128From.memBytes_split n (s.toNat - 40) 4 ft (by omega) $$ FT
  icases FT with ⟨FTt, FTd⟩
  ihave W := joinB (a := s.toNat - 44) (b := s.toNat - 40) f52 (ft.take 4) (by omega) $$ [F52 FTt]
  · ihave F52 := memBytes_addr (b := s.toNat - 44) (by omega) $$ F52
    iframe F52 FTt
  mstep; mstep [W]; mstep
  icases splitB (a := s.toNat - 44) (b := s.toNat - 40) f52 (ft.take 4) (by omega) $$ W with ⟨F52, FTt⟩
  mstep; mstep [T48]; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  ihave Src := joinB (a := s.toNat - 40 + 4) (b := s.toNat - 4) (ft.drop 4) f92 (by simp; omega) $$ [FTd F92]
  · ihave F92 := memBytes_addr (b := s.toNat - 4) (by omega) $$ F92
    iframe FTd F92
  mcall (M36 (s - 96 + 12) (s - 96 + 48 + 12) 36 (by omega) (by omega) f12 (ft.drop 4 ++ f92) hf12
      (by simp; omega) (by omega) (by omega)) using [F12 Src]
  · iunfold MemCpy.pre
    ihave F12 := memBytes_addr (b := (s - 96 + 12).toNat) (by omega) $$ F12
    ihave Src := memBytes_addr (b := (s - 96 + 48 + 12).toNat) (by omega) $$ Src
    iframe F12 Src
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, D12, Src⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [Ho8]
  rw [store32_hi f52 (ft.take 4) hf52 (by simp; omega)]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (M36 (out + 12) (s - 96 + 12) 36 (by omega) (by omega) (o8.drop 4) (ft.drop 4 ++ f92) (by simp; omega)
      (by simp; omega) (by simp [UInt32.toNat_add]; omega) (by omega)) using [Ho12 D12]
  · iunfold MemCpy.pre
    ihave Ho12 := memBytes_addr (b := (out + 12).toNat) (by simp [UInt32.toNat_add]; omega) $$ Ho12
    iframe Ho12 D12
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Ho12, D12⟩
  subst hrs
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep [Ho0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 96 + 96 = s by simp]
  mcredits R
  ihave Ho8 := joinB (a := out.toNat + 8) (b := (out + 12).toNat) (ft.take 4) (ft.drop 4 ++ f92)
    (by simp [UInt32.toNat_add]; omega) $$ [Ho8 Ho12]
  · iframe Ho8 Ho12
  rw [← List.append_assoc, List.take_append_drop] at *
  ihave CA : contractAt n maxP len live (out.toNat + 8) b0 b1 c0 pre $$ [Ho8 HW]
  · subst hftd
    iunfold contractAt
    iexists p, f92
    iframe Ho8 HW
    ipureintro; exact hf92
  ihave Lo := stkA (b := s.toNat - 352) (by omega) $$ Lo
  ihave D12 := stkB (b := s.toNat - 84) (k := 36) _ (by omega) (by simp; omega) $$ D12
  ihave T48 := stkW (b := s.toNat - 48) _ (by omega) $$ T48
  ihave F52 := stkB (b := s.toNat - 44) (k := 4) _ (by omega) hf52 $$ F52
  ihave FTt := stkB (b := s.toNat - 40) (k := 4) _ (by omega) (by simp; omega) $$ FTt
  ihave Src := stkB (b := s.toNat - 36) (k := 36) _ (by omega) (by simp; omega) $$ Src
  ihave FTt := stkJ (a := s.toNat - 40) (b := s.toNat - 36) (k1 := 4) (k2 := 36) (k := 40) (by omega) rfl $$ [FTt Src]
  · iframe FTt Src
  ihave F52 := stkJ (a := s.toNat - 44) (b := s.toNat - 40) (k1 := 4) (k2 := 40) (k := 44) (by omega) rfl $$ [F52 FTt]
  · iframe F52 FTt
  ihave T48 := stkJ (a := s.toNat - 48) (b := s.toNat - 44) (k1 := 4) (k2 := 44) (k := 48) (by omega) rfl $$ [T48 F52]
  · iframe T48 F52
  ihave D12 := stkJ (a := s.toNat - 84) (b := s.toNat - 48) (k1 := 36) (k2 := 48) (k := 84) (by omega) rfl $$ [D12 T48]
  · iframe D12 T48
  ihave F0 := stkJ (a := s.toNat - 352 + 256) (b := s.toNat - 84) (k1 := 12) (k2 := 84) (k := 96) (by omega) rfl $$ [F0 D12]
  · iframe F0 D12
  ihave Stk := stkJ (a := s.toNat - 352) (b := s.toNat - 352 + 256) (k1 := 256) (k2 := 96) (k := 352) (by omega) rfl $$ [Lo F0]
  · iframe Lo F0
  iframe Hc
  iunfold post162
  iframe Hg Stk Hvt Hr Ho0 CA Hd4 Hpre B0 B1 C0
  ipureintro; simp [htype]

theorem or4 (x : UInt32) (h : x.toNat % 8 = 0) : (x ||| 4).toNat = x.toNat + 4 := by
  rw [UInt32.toNat_or]
  obtain ⟨k, hk⟩ : ∃ k, x.toNat = 8 * k := ⟨x.toNat / 8, by omega⟩
  rw [hk]
  have := Nat.two_pow_add_eq_or_of_lt (i := 3) (b := 4) (by norm_num) k
  simp at this ⊢
  omega

/-- The code `try_from_slice` runs (persistent). -/
def sliceCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(contractCode n maxP inst mi A ∗ A 161 ↪[wf] FuncInst.wasm types[31]! inst f161)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (sliceCode (GF := GF) n maxP inst mi A) := by
  unfold sliceCode; infer_instance

def pre161 (n g : Nat) (gt : GlobalType) (s out q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (o0 o8 hd pre b0 b1 c0 : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 q, .i32 m]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 496) 496 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗
    n ↦[wms][ out.toNat ] o0 ∗ n ↦[wms][ out.toNat + 8 ] o8 ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] pre ∗ n ↦[wms][ q.toNat + 4 + pre.length ] b0 ∗
    n ↦[wms][ q.toNat + 4 + pre.length + 8 ] b1 ∗ n ↦[wms][ q.toNat + 4 + pre.length + 16 ] c0)

def post161 (n g : Nat) (gt : GlobalType) (s out q : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (hd pre b0 b1 c0 : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 496) 496 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] 0 ∗ contractAt n maxP len live (out.toNat + 8) b0 b1 c0 pre ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] pre ∗ n ↦[wms][ q.toNat + 4 + pre.length ] b0 ∗
    n ↦[wms][ q.toNat + 4 + pre.length + 8 ] b1 ∗ n ↦[wms][ q.toNat + 4 + pre.length + 16 ] c0)

/-- The cost of `try_from_slice` with a prefix of `L` bytes. -/
def cost161 (cfg : WasmConfig) (L : UInt32) : Nat :=
  115 * cfg.regularOpCost + (93 * cfg.regularOpCost + cost425 cfg L + 654 * cfg.regularOpCost +
    654 * cfg.regularOpCost) + 654 * cfg.regularOpCost + 654 * cfg.regularOpCost + 726 * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`BorshDeserialize::try_from_slice::<Contract>`** (161) on the `len` bytes at `q`,
`hd ++ pre ++ b0 ++ b1 ++ c0` exactly (`len = 4 + |pre| + 24`): `Ok` and the `Contract`
(`contractAt`) at `out`. -/
theorem f161_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out q m : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o0 o8 hd4 pre b0 b1 c0 : List UInt8) (ho0 : o0.length = 4) (ho8 : o8.length = 40) (hhd : hd4.length = 4)
    (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hc0 : c0.length = 8)
    (hL : Memory.decodeLE hd4 = pre.length) (hL0 : 0 < pre.length) (hL28 : pre.length < 2 ^ 28)
    (hroom : roomFor len maxP (UInt32.ofNat pre.length))
    (hs : 496 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hmL : m.toNat = 4 + pre.length + 24)
    (hq : q.toNat + 4 + pre.length + 24 ≤ 2 ^ 32) (hout : out.toNat + 48 ≤ 2 ^ 32) :
    sliceCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f161 Cg
        (pre161 n g gt s out q m idx ta (A 578) maxP len live o0 o8 hd4 pre b0 b1 c0)
        (fun _ => cost161 cfg (UInt32.ofNat pre.length))
        (post161 n g gt s out q idx ta (A 578) maxP len live hd4 pre b0 b1 c0) := by
  iintro #Hcode
  ihave #Hcode' := Hcode
  iunfold sliceCode at Hcode'
  icases Hcode' with ⟨#Hct, -⟩
  ihave #Hct' := Hct
  iunfold contractCode at Hct'
  icases Hct' with ⟨#Hft, -, #H951, #H162⟩
  ihave #Hft' := Hft
  iunfold ftCode, bytesCode, rdCode at Hft'
  icases Hft' with ⟨⟨⟨#Hi, -⟩, -⟩, -⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha162 := hm.funcs 162 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have hmlt := m.toNat_lt
  have h144 : (s - 144).toNat = s.toNat - 144 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 144 + 8).toNat = s.toNat - 136 := by simp [UInt32.toNat_add, h144]; omega
  have e16 : (s - 144 + 16).toNat = s.toNat - 128 := by simp [UInt32.toNat_add, h144]; omega
  have e20 : (s - 144 + 16 ||| 4).toNat = s.toNat - 124 := by rw [or4 _ (by omega)]; omega
  have e60 : (s - 144 + 60).toNat = s.toNat - 84 := by simp [UInt32.toNat_add, h144]; omega
  have e96 : (s - 144 + 96).toNat = s.toNat - 48 := by simp [UInt32.toNat_add, h144]; omega
  have e108 : (s - 144 + 108).toNat = s.toNat - 36 := by simp [UInt32.toNat_add, h144]; omega
  have hLn : (UInt32.ofNat pre.length).toNat = pre.length := by simp; omega
  have hm0 : m - 4 - UInt32.ofNat pre.length - 16 - 8 = 0 := by
    apply UInt32.toNat_inj.mp
    have h4 : (m - 4).toNat = m.toNat - 4 := by
      rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
    have h5 : (m - 4 - UInt32.ofNat pre.length).toNat = m.toNat - 4 - pre.length := by
      rw [UInt32.toNat_sub_of_le, h4, hLn]; rw [UInt32.le_iff_toNat_le, h4, hLn]; omega
    have h6 : (m - 4 - UInt32.ofNat pre.length - 16).toNat = 8 := by
      rw [UInt32.toNat_sub_of_le, h5]
      · simp; omega
      rw [UInt32.le_iff_toNat_le, h5]; simp; omega
    rw [UInt32.toNat_sub_of_le, h6]
    · rfl
    rw [UInt32.le_iff_toNat_le, h6]; simp
  have M36 := memcpy_spec (GF := GF) cfg lim (d + 1) inst mi n hn Cg
  unfold cost161
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre161 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho0, Ho8, Hd4, Hpre, B0, B1, C0⟩
  subst hargs
  icases stkSp 352 144 rfl $$ Hs with ⟨Lo, Hs⟩
  icases stkSp 8 136 rfl $$ Hs with ⟨F0, Hs⟩
  icases stkSp 4 132 rfl $$ Hs with ⟨R8, Hs⟩
  icases stkSp 4 128 rfl $$ Hs with ⟨R12, Hs⟩
  icases stkSp 4 124 rfl $$ Hs with ⟨F16, Hs⟩
  icases stkSp 36 88 rfl $$ Hs with ⟨F20, Hs⟩
  icases stkSp 4 84 rfl $$ Hs with ⟨F56, Hs⟩
  icases stkSp 36 48 rfl $$ Hs with ⟨F60, Hs⟩
  icases stkSp 4 44 rfl $$ Hs with ⟨F96, Hs⟩
  icases stkSp 4 40 rfl $$ Hs with ⟨F100, F104⟩
  icases stk_bytes' $$ R8 with ⟨%r8, %hr8, R8⟩
  icases stk_bytes' $$ R12 with ⟨%r12, %hr12, R12⟩
  icases stk_bytes' $$ F16 with ⟨%f16, %hf16, F16⟩
  icases stk_bytes' $$ F20 with ⟨%f20, %hf20, F20⟩
  icases stk_bytes' $$ F60 with ⟨%f60, %hf60, F60⟩
  icases stk_bytes' $$ F96 with ⟨%f96, %hf96, F96⟩
  icases stk_bytes' $$ F100 with ⟨%f100, %hf100, F100⟩
  icases stk_bytes' $$ F104 with ⟨%f104, %hf104, F104⟩
  ihave R8 := memBytes_addr (b := s.toNat - 136) (by omega) $$ R8
  ihave R12 := memBytes_addr (b := s.toNat - 132) (by omega) $$ R12
  ihave F16 := memBytes_addr (b := s.toNat - 128) (by omega) $$ F16
  ihave F20 := memBytes_addr (b := s.toNat - 124) (by omega) $$ F20
  ihave F60 := memBytes_addr (b := s.toNat - 84) (by omega) $$ F60
  ihave F96 := memBytes_addr (b := s.toNat - 48) (by omega) $$ F96
  ihave F100 := memBytes_addr (b := s.toNat - 44) (by omega) $$ F100
  ihave F104 := memBytes_addr (b := s.toNat - 40) (by omega) $$ F104
  simp only [f161]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [R12]
  mstep; mstep; mstep [R8]
  mstep; mstep; mstep; mstep; mstep; mstep
  ihave Rd := join64' (a := s.toNat - 136) (b := s.toNat - 132) q m (by omega) $$ [R8 R12]
  · iframe R8 R12
  mcall (f162_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 144) (s - 144 + 96)
      (s - 144 + 8) q m idx maxP len live f96 f104 hd4 pre b0 b1 c0 hf96 hf104 hhd hb0 hb1 hc0 hL hL0 hL28 hroom
      (by omega) (by omega) hq (by omega) (by omega))
    using [Hg Lo Hvt Hinv Rd F96 F104 Hd4 Hpre B0 B1 C0]
  · iunfold pre162, rdr
    ihave Lo := stkA (b := (s - 144).toNat - 352) (by omega) $$ Lo
    ihave Rd := memBytes_addr (b := (s - 144 + 8).toNat) (by omega) $$ Rd
    ihave F96 := memBytes_addr (b := (s - 144 + 96).toNat) (by omega) $$ F96
    ihave F104 := memBytes_addr (b := (s - 144 + 96).toNat + 8) (by omega) $$ F104
    iframe Hg Lo Hvt Hinv Rd F96 F104 Hd4 Hpre B0 B1 C0
    ipureintro; rfl
  iunfold post162 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hr, T96, CA, Hd4, Hpre, B0, B1, C0⟩
  subst hrs
  iunfold contractAt at CA
  icases CA with ⟨%p, %pad, %hpad, FT, HW⟩
  have hft : (ftHead b0 b1 c0 p pre ++ pad).length = 40 := by
    rw [List.length_append, ftHead_length b0 b1 c0 p pre hb0 hb1 hc0, hpad]
  generalize hftd : ftHead b0 b1 c0 p pre ++ pad = ft at hft ⊢
  ihave FT := memBytes_addr (b := s.toNat - 40) (by omega) $$ FT
  ihave FT := U128From.memBytes_split n (s.toNat - 40) 4 ft (by omega) $$ FT
  icases FT with ⟨FTt, FTd⟩
  ihave W := joinB (a := s.toNat - 44) (b := s.toNat - 40) f100 (ft.take 4) (by omega) $$ [F100 FTt]
  · iframe F100 FTt
  mstep; mstep [W]; mstep
  icases splitB (a := s.toNat - 44) (b := s.toNat - 40) f100 (ft.take 4) (by omega) $$ W with ⟨F100, FTt⟩
  ihave T96 := memBytes_addr (b := s.toNat - 48) (by omega) $$ T96
  mstep; mstep [T96]; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (M36 (s - 144 + 60) (s - 144 + 108) 36 (by omega) (by omega) f60 (ft.drop 4) hf60
      (by simp; omega) (by omega) (by omega)) using [F60 FTd]
  · iunfold MemCpy.pre
    ihave F60 := memBytes_addr (b := (s - 144 + 60).toNat) (by omega) $$ F60
    ihave FTd := memBytes_addr (b := (s - 144 + 108).toNat) (by omega) $$ FTd
    iframe F60 FTd
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, F60, FTd⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep [F16]
  rw [store32_hi f100 (ft.take 4) hf100 (by simp; omega)]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (M36 (s - 144 + 16 ||| 4) (s - 144 + 60) 36 (by omega) (by omega) f20 (ft.drop 4) hf20
      (by simp; omega) (by omega) (by omega)) using [F20 F60]
  · iunfold MemCpy.pre
    ihave F20 := memBytes_addr (b := (s - 144 + 16 ||| 4).toNat) (by omega) $$ F20
    iframe F20 F60
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, F20, F60⟩
  subst hrs
  iunfold rdr at Hr
  rw [hm0]
  ihave Hr := memBytes_addr (b := s.toNat - 136) (by omega) $$ Hr
  icases split64' (a := s.toNat - 136) (b := s.toNat - 132) _ _ (by omega) $$ Hr with ⟨R8, R12⟩
  mstep; mstep; mstep; mstep [R12]; mstep; mstep
  ihave F16 := joinB (a := s.toNat - 128) (b := (s - 144 + 16 ||| 4).toNat) (ft.take 4) (ft.drop 4)
    (by rw [e20, List.length_take]; omega) $$ [F16 F20]
  · iframe F16 F20
  rw [List.take_append_drop]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (M36 (out + 8) (s - 144 + 16) 40 (by omega) (by omega) o8 ft ho8 hft
      (by simp [UInt32.toNat_add]; omega) (by omega)) using [Ho8 F16]
  · iunfold MemCpy.pre
    ihave Ho8 := memBytes_addr (b := (out + 8).toNat) (by simp [UInt32.toNat_add]; omega) $$ Ho8
    ihave F16 := memBytes_addr (b := (s - 144 + 16).toNat) (by omega) $$ F16
    iframe Ho8 F16
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Ho8, F16⟩
  subst hrs
  mstep; mstep; mstep; mstep [Ho0]; mstep
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 144 + 144 = s by simp]
  mcredits R
  ihave Ho8 := memBytes_addr (b := out.toNat + 8) (by simp [UInt32.toNat_add]; omega) $$ Ho8
  ihave Lo := stkA (b := s.toNat - 496) (by omega) $$ Lo
  ihave F0 := stkA (b := s.toNat - 144) (by omega) $$ F0
  ihave F56 := stkA (b := s.toNat - 88) (by omega) $$ F56
  ihave R8 := stkW (b := s.toNat - 136) _ rfl $$ R8
  ihave R12 := stkW (b := s.toNat - 132) _ rfl $$ R12
  ihave F16 := stkB (b := s.toNat - 128) (k := 40) _ (by omega) hft $$ F16
  ihave F60 := stkB (b := s.toNat - 84) (k := 36) _ (by omega) (by simp; omega) $$ F60
  ihave T96 := stkW (b := s.toNat - 48) _ rfl $$ T96
  ihave F100 := stkB (b := s.toNat - 44) (k := 4) _ rfl hf100 $$ F100
  ihave FTt := stkB (b := s.toNat - 40) (k := 4) _ rfl (by simp; omega) $$ FTt
  ihave FTd := stkB (b := s.toNat - 36) (k := 36) _ (by omega) (by simp; omega) $$ FTd
  ihave FTt := stkJ (a := s.toNat - 40) (b := s.toNat - 36) (k1 := 4) (k2 := 36) (k := 40) (by omega) rfl $$ [FTt FTd]
  · iframe FTt FTd
  ihave F100 := stkJ (a := s.toNat - 44) (b := s.toNat - 40) (k1 := 4) (k2 := 40) (k := 44) (by omega) rfl $$ [F100 FTt]
  · iframe F100 FTt
  ihave T96 := stkJ (a := s.toNat - 48) (b := s.toNat - 44) (k1 := 4) (k2 := 44) (k := 48) (by omega) rfl $$ [T96 F100]
  · iframe T96 F100
  ihave F60 := stkJ (a := s.toNat - 84) (b := s.toNat - 48) (k1 := 36) (k2 := 48) (k := 84) (by omega) rfl $$ [F60 T96]
  · iframe F60 T96
  ihave F56 := stkJ (a := s.toNat - 88) (b := s.toNat - 84) (k1 := 4) (k2 := 84) (k := 88) (by omega) rfl $$ [F56 F60]
  · iframe F56 F60
  ihave F16 := stkJ (a := s.toNat - 128) (b := s.toNat - 88) (k1 := 40) (k2 := 88) (k := 128) (by omega) rfl $$ [F16 F56]
  · iframe F16 F56
  ihave R12 := stkJ (a := s.toNat - 132) (b := s.toNat - 128) (k1 := 4) (k2 := 128) (k := 132) (by omega) rfl $$ [R12 F16]
  · iframe R12 F16
  ihave R8 := stkJ (a := s.toNat - 136) (b := s.toNat - 132) (k1 := 4) (k2 := 132) (k := 136) (by omega) rfl $$ [R8 R12]
  · iframe R8 R12
  ihave F0 := stkJ (a := s.toNat - 144) (b := s.toNat - 136) (k1 := 8) (k2 := 136) (k := 144) (by omega) rfl $$ [F0 R8]
  · iframe F0 R8
  ihave Stk := stkJ (a := s.toNat - 496) (b := s.toNat - 144) (k1 := 352) (k2 := 144) (k := 496) (by omega) rfl $$ [Lo F0]
  · iframe Lo F0
  ihave CA : contractAt n maxP len live (out.toNat + 8) b0 b1 c0 pre $$ [Ho8 HW]
  · subst hftd
    iunfold contractAt
    iexists p, pad
    iframe Ho8 HW
    ipureintro; exact hpad
  iframe Hc
  iunfold post161
  iframe Hg Stk Hvt Ho0 CA Hd4 Hpre B0 B1 C0
  ipureintro; simp [htype]

end Spec

end WNear.Binary.BorshContract
