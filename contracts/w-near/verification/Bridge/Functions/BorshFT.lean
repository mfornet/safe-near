import Bridge.Functions.BorshBytes

/-!
# `<FungibleToken as BorshDeserialize>::deserialize` (425)

```wat
;; 425 (out, r): sp -= 96
;;     315(sp + 56, r)                      ;; the LookupMap prefix: Vec<u8> (p, L, L) at sp + 60
;;     [sp+16..28) := the Vec; 372(sp + 56, r)          ;; total_supply: u128 at sp + 64
;;     shuffles through [sp+32..52); hi := [sp+44] (i64), lo := [sp+36] (i64)
;;     371(sp + 56, r)                      ;; account_storage_usage: u64 at sp + 64
;;     shuffles through [sp+80..92); v := [sp+84] (i64); [sp..12) := the Vec
;;     out+8 := lo; out+16 := hi; out+24 := v; out+32 := (p, L) (i64); out+40 := L; out := 0 (Ok)
```

The `Err` arms (and the drop of the prefix `Vec` on them, 321) are not on our path: the
precondition gives the bytes `u32 L ++ prefix ++ supply (16) ++ usage (8)` at the reader.

* `f425_spec`: `Ok` at `out` and the `FungibleToken` `ftHead b0 b1 c0 p prefix` at `out + 8`
  (supply, usage, the `Vec` `(p, L, L)`), `p` a fresh live block holding the prefix
  (`heapWith`), the reader advanced by `4 + L + 24`.
-/

namespace WNear.Binary.BorshFT

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.BorshLeaves WNear.Binary.BorshInt WNear.Binary.BorshVec WNear.Binary.BorshBytes
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro pair64 storeBytes_pair64
  ofNat_decode_pair roomFor grownLen)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.Interface (IfaceMod)

/-- Eight bytes as two words. -/
theorem split8 (b : List UInt8) (h : b.length = 8) : ∃ x0 x1 : UInt32, b = bytes32 x0 ++ bytes32 x1 := by
  refine ⟨UInt32.ofNat (Memory.decodeLE (b.take 4)), UInt32.ofNat (Memory.decodeLE (b.drop 4)), ?_⟩
  rw [← ReadRegister.bytes32_of _ (by simp; omega), ← ReadRegister.bytes32_of _ (by simp; omega)]
  simp

/-- The 36 bytes of a `FungibleToken` that `deserialize` writes: `total_supply` (`b0 ++ b1`),
`account_storage_usage` (`c0`) and the prefix `Vec` `(p, L, L)`. -/
def ftHead (b0 b1 c0 : List UInt8) (p : UInt32) (pre : List UInt8) : List UInt8 :=
  b0 ++ b1 ++ c0 ++ bytes32 p ++ bytes32 (UInt32.ofNat pre.length) ++ bytes32 (UInt32.ofNat pre.length)

theorem ftHead_length (b0 b1 c0 : List UInt8) (p : UInt32) (pre : List UInt8) (h0 : b0.length = 8)
    (h1 : b1.length = 8) (h2 : c0.length = 8) : (ftHead b0 b1 c0 p pre).length = 36 := by
  simp [ftHead, h0, h1, h2]

section Helpers

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem join64' {n a b : Nat} (x y : UInt32) (h : b = a + 4) :
    n ↦[i32][ a ] x ∗ n ↦[i32][ b ] y ⊢ (n ↦[wms][ a ] (bytes32 x ++ bytes32 y) : IProp GF) := by
  subst h; exact KeyGet.join64 n a x y

theorem split64' {n a b : Nat} (x y : UInt32) (h : b = a + 4) :
    (n ↦[wms][ a ] (bytes32 x ++ bytes32 y) : IProp GF) ⊢ n ↦[i32][ a ] x ∗ n ↦[i32][ b ] y := by
  subst h; exact KeyGet.split64 n a x y

theorem joinB {n a b : Nat} (xs ys : List UInt8) (h : b = a + xs.length) :
    n ↦[wms][ a ] xs ∗ n ↦[wms][ b ] ys ⊢ (n ↦[wms][ a ] (xs ++ ys) : IProp GF) := by
  subst h; exact U128From.memBytes_join n a xs.length xs ys rfl

theorem splitB {n a b : Nat} (xs ys : List UInt8) (h : b = a + xs.length) :
    (n ↦[wms][ a ] (xs ++ ys) : IProp GF) ⊢ n ↦[wms][ a ] xs ∗ n ↦[wms][ b ] ys := by
  subst h
  have e := memBytes_append (GF := GF) (H := NearState) n a xs ys
  exact e.1

theorem stkJ {n a b k1 k2 k : Nat} (h : b = a + k1) (hk : k = k1 + k2) :
    stk (GF := GF) n a k1 ∗ stk n b k2 ⊢ stk n a k := by
  subst h hk; exact stk_join n a k1 k2

theorem stkW {n a b : Nat} (w : UInt32) (h : a = b) : n ↦[i32][ a ] w ⊢ stk (GF := GF) n b 4 := by
  subst h; exact stk_word n a w

theorem stkB {n a b k : Nat} (bs : List UInt8) (h : a = b) (hl : bs.length = k) :
    n ↦[wms][ a ] bs ⊢ stk (GF := GF) n b k := by
  subst h; exact ReadRegister.stk_bytes n a bs k hl

theorem stkSp {n a k : Nat} (k1 k2 : Nat) (hk : k = k1 + k2) :
    stk (GF := GF) n a k ⊢ stk n a k1 ∗ stk n (a + k1) k2 := by
  subst hk; exact stk_split n a k1 k2

theorem stkA {n a b k : Nat} (h : a = b) : stk (GF := GF) n a k ⊢ stk n b k := by
  subst h; exact .rfl

end Helpers

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The heap after the prefix's allocation: `p` live, holding `data`. -/
def heapWith (n maxP len : Nat) (live : List (Nat × Nat)) (p : UInt32) (data : List UInt8) : IProp GF :=
  iprop(∃ len', ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len (UInt32.ofNat data.length))⌝ ∗
    heapInv n maxP len' ((p.toNat, data.length) :: live) 1 ∗ n ↦[wms][ p.toNat ] data)

/-- The code `deserialize` runs (persistent). -/
def ftCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(bytesCode n maxP inst mi A ∗ A 315 ↪[wf] FuncInst.wasm types[14]! inst f315 ∗
    A 372 ↪[wf] FuncInst.wasm types[14]! inst f372 ∗ A 371 ↪[wf] FuncInst.wasm types[14]! inst f371)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (ftCode (GF := GF) n maxP inst mi A) := by
  unfold ftCode; infer_instance

def pre425 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (o0 o8 hd pre b0 b1 c0 : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 r]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 256) 256 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗ rdr n r q m ∗
    n ↦[wms][ out.toNat ] o0 ∗ n ↦[wms][ out.toNat + 8 ] o8 ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] pre ∗ n ↦[wms][ q.toNat + 4 + pre.length ] b0 ∗
    n ↦[wms][ q.toNat + 4 + pre.length + 8 ] b1 ∗ n ↦[wms][ q.toNat + 4 + pre.length + 16 ] c0)

def post425 (n g : Nat) (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (hd pre b0 b1 c0 : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 256) 256 ∗ vt n 1057464 idx ta a578 ∗
    rdr n r (q + 4 + UInt32.ofNat pre.length + 16 + 8) (m - 4 - UInt32.ofNat pre.length - 16 - 8) ∗
    n ↦[i32][ out.toNat ] 0 ∗ (∃ p : UInt32, n ↦[wms][ out.toNat + 8 ] ftHead b0 b1 c0 p pre ∗
      heapWith n maxP len live p pre) ∗
    n ↦[wms][ q.toNat ] hd ∗ n ↦[wms][ q.toNat + 4 ] pre ∗ n ↦[wms][ q.toNat + 4 + pre.length ] b0 ∗
    n ↦[wms][ q.toNat + 4 + pre.length + 8 ] b1 ∗ n ↦[wms][ q.toNat + 4 + pre.length + 16 ] c0)

/-- The cost of `deserialize` with a prefix of `L` bytes. -/
def cost425 (cfg : WasmConfig) (L : UInt32) : Nat :=
  182 * cfg.regularOpCost + (53 * cfg.regularOpCost + (260 * cfg.regularOpCost + cost374 cfg L)) +
    154 * cfg.regularOpCost + 138 * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`<FungibleToken as BorshDeserialize>::deserialize`** (425) on
`hd ++ pre ++ b0 ++ b1 ++ c0` at the reader (`hd` the `u32` length of `pre`). -/
theorem f425_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out r q m : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o0 o8 hd4 pre b0 b1 c0 : List UInt8) (ho0 : o0.length = 4) (ho8 : o8.length = 36) (hhd : hd4.length = 4)
    (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hc0 : c0.length = 8)
    (hL : Memory.decodeLE hd4 = pre.length) (hL0 : 0 < pre.length) (hL28 : pre.length < 2 ^ 28)
    (hroom : roomFor len maxP (UInt32.ofNat pre.length))
    (hs : 256 ≤ s.toNat) (hmL : 4 + pre.length + 24 ≤ m.toNat)
    (hq : q.toNat + 4 + pre.length + 24 ≤ 2 ^ 32) (hout : out.toNat + 44 ≤ 2 ^ 32) (hr : r.toNat + 8 ≤ 2 ^ 32) :
    ftCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f425 Cg
        (pre425 n g gt s out r q m idx ta (A 578) maxP len live o0 o8 hd4 pre b0 b1 c0)
        (fun _ => cost425 cfg (UInt32.ofNat pre.length))
        (post425 n g gt s out r q m idx ta (A 578) maxP len live hd4 pre b0 b1 c0) := by
  iintro #Hcode
  ihave #Hcode' := Hcode
  iunfold ftCode at Hcode'
  icases Hcode' with ⟨#Hby, #H315, #H372, #H371⟩
  ihave #Hby' := Hby
  iunfold bytesCode at Hby'
  icases Hby' with ⟨#Hrd, -, -, -⟩
  ihave #Hrd' := Hrd
  iunfold rdCode at Hrd'
  icases Hrd' with ⟨#Hi, -⟩
  obtain ⟨x0, x1, rfl⟩ := split8 b0 hb0
  obtain ⟨y0, y1, rfl⟩ := split8 b1 hb1
  obtain ⟨z0, z1, rfl⟩ := split8 c0 hc0
  have hn := hm.mem
  have hg := hm.glob
  have ha315 := hm.funcs 315 (by decide)
  have ha372 := hm.funcs 372 (by decide)
  have ha371 := hm.funcs 371 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have hmlt := m.toNat_lt
  have hqlt := q.toNat_lt
  have h96 : (s - 96).toNat = s.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e56 : (s - 96 + 56).toNat = s.toNat - 40 := by simp [UInt32.toNat_add, h96]; omega
  have hLn : (UInt32.ofNat pre.length).toNat = pre.length := by simp; omega
  have hq1 : (q + 4 + UInt32.ofNat pre.length).toNat = q.toNat + 4 + pre.length := by
    simp [UInt32.toNat_add]; omega
  have hm1 : (m - 4 - UInt32.ofNat pre.length).toNat = m.toNat - 4 - pre.length := by
    have h4 : (m - 4).toNat = m.toNat - 4 := by
      rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
    rw [UInt32.toNat_sub_of_le, h4, hLn]
    rw [UInt32.le_iff_toNat_le, h4, hLn]; omega
  have hq2 : (q + 4 + UInt32.ofNat pre.length + 16).toNat = q.toNat + 4 + pre.length + 16 := by
    rw [UInt32.toNat_add, hq1]; simp; omega
  have hm2 : (m - 4 - UInt32.ofNat pre.length - 16).toNat = m.toNat - 4 - pre.length - 16 := by
    rw [UInt32.toNat_sub_of_le, hm1]
    · simp
    rw [UInt32.le_iff_toNat_le, hm1]; simp; omega
  iapply MFunSpec_intro
  imodintro
  unfold cost425
  iintro %args %R HP Hc
  iunfold pre425 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hr, Ho0, Ho8, Hd4, Hpre, B0, B1, C0⟩
  subst hargs
  -- out: [0, 4) [8, 16) [16, 24) [24, 32) [32, 40) [40, 44)
  ihave Ho8 := U128From.memBytes_split n (out.toNat + 8) 8 o8 (by omega) $$ Ho8
  icases Ho8 with ⟨Ho8, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 8 + 8) 8 (o8.drop 8) (by simp; omega) $$ Ho
  icases Ho with ⟨Ho16, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 8 + 8 + 8) 8 ((o8.drop 8).drop 8) (by simp; omega) $$ Ho
  icases Ho with ⟨Ho24, Ho⟩
  ihave Ho := U128From.memBytes_split n (out.toNat + 8 + 8 + 8 + 8) 8 (((o8.drop 8).drop 8).drop 8)
    (by simp; omega) $$ Ho
  icases Ho with ⟨Ho32, Ho40⟩
  rw [show out.toNat + 8 + 8 = out.toNat + 16 by omega, show out.toNat + 16 + 8 = out.toNat + 24 by omega,
    show out.toNat + 24 + 8 = out.toNat + 32 by omega, show out.toNat + 32 + 8 = out.toNat + 40 by omega]
  -- the stack: 160 below the frame (the top 48 for 372 and 371), then the frame
  icases stk_split n (s.toNat - 256) 160 96 $$ Hs with ⟨Lo, Hs⟩
  rw [show s.toNat - 256 + 160 = s.toNat - 96 by omega]
  icases stk_split n (s.toNat - 96) 8 88 $$ Hs with ⟨F0, Hs⟩
  icases stk_split n (s.toNat - 96 + 8) 4 84 $$ Hs with ⟨F8, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4) 4 80 $$ Hs with ⟨F12, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4) 8 72 $$ Hs with ⟨F16, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8) 4 68 $$ Hs with ⟨F24, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4) 4 64 $$ Hs with ⟨F28, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4 + 4) 8 56 $$ Hs with ⟨F32, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4 + 4 + 8) 8 48 $$ Hs with ⟨F40, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4 + 4 + 8 + 8) 4 44 $$ Hs with ⟨F48, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4 + 4 + 8 + 8 + 4) 4 40 $$ Hs with ⟨F52, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4 + 4 + 8 + 8 + 4 + 4) 16 24 $$ Hs with ⟨F56, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4 + 4 + 8 + 8 + 4 + 4 + 16) 8 16 $$ Hs with ⟨F72, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4 + 4 + 8 + 8 + 4 + 4 + 16 + 8) 8 8 $$ Hs with ⟨F80, Hs⟩
  icases stk_split n (s.toNat - 96 + 8 + 4 + 4 + 8 + 4 + 4 + 8 + 8 + 4 + 4 + 16 + 8 + 8) 4 4 $$ Hs with ⟨F88, F92⟩
  rw [show s.toNat - 96 + 8 = s.toNat - 88 by omega, show s.toNat - 88 + 4 = s.toNat - 84 by omega,
    show s.toNat - 84 + 4 = s.toNat - 80 by omega, show s.toNat - 80 + 8 = s.toNat - 72 by omega,
    show s.toNat - 72 + 4 = s.toNat - 68 by omega, show s.toNat - 68 + 4 = s.toNat - 64 by omega,
    show s.toNat - 64 + 8 = s.toNat - 56 by omega, show s.toNat - 56 + 8 = s.toNat - 48 by omega,
    show s.toNat - 48 + 4 = s.toNat - 44 by omega, show s.toNat - 44 + 4 = s.toNat - 40 by omega,
    show s.toNat - 40 + 16 = s.toNat - 24 by omega, show s.toNat - 24 + 8 = s.toNat - 16 by omega,
    show s.toNat - 16 + 8 = s.toNat - 8 by omega, show s.toNat - 8 + 4 = s.toNat - 4 by omega]
  icases stk_bytes' $$ F0 with ⟨%f0, %hf0, F0⟩
  icases stk_bytes' $$ F8 with ⟨%f8, %hf8, F8⟩
  icases stk_bytes' $$ F16 with ⟨%f16, %hf16, F16⟩
  icases stk_bytes' $$ F24 with ⟨%f24, %hf24, F24⟩
  icases stk_bytes' $$ F32 with ⟨%f32, %hf32, F32⟩
  icases stk_bytes' $$ F40 with ⟨%f40, %hf40, F40⟩
  icases stk_bytes' $$ F48 with ⟨%f48, %hf48, F48⟩
  icases stk_bytes' $$ F56 with ⟨%f56, %hf56, F56⟩
  icases stk_bytes' $$ F72 with ⟨%f72, %hf72, F72⟩
  icases stk_bytes' $$ F80 with ⟨%f80, %hf80, F80⟩
  icases stk_bytes' $$ F88 with ⟨%f88, %hf88, F88⟩
  simp only [f425]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (f315_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 96) (s - 96 + 56)
      r q m idx maxP len live f56 hd4 pre hf56 hhd hL hL0 hL28 hroom (by omega) (by omega) (by omega) (by omega) hr)
    using [Hg Lo Hvt Hinv Hr F56 Hd4 Hpre]
  · iunfold pre315
    ihave Lo := stk_addr (show s.toNat - 256 = (s - 96).toNat - 160 by omega) $$ Lo
    ihave F56 := memBytes_addr (show s.toNat - 40 = (s - 96 + 56).toNat by omega) $$ F56
    iframe Hg Lo Hvt Hinv Hr F56 Hd4 Hpre
    ipureintro; rfl
  iunfold post315 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hr, V56, VV, Hd4, Hpre⟩
  subst hrs
  iunfold vecAt at VV
  icases VV with ⟨%p, V60, V64, V68, %len', %hl', Hinv, Hb⟩
  ihave V56 := memBytes_addr (a := (s - 96 + 56).toNat) (b := s.toNat - 40) (by omega) $$ V56
  ihave V60 := memBytes_addr (a := (s - 96 + 56).toNat + 4) (b := s.toNat - 36) (by omega) $$ V60
  ihave V64 := memBytes_addr (a := (s - 96 + 56).toNat + 4 + 4) (b := s.toNat - 32) (by omega) $$ V64
  ihave V68 := memBytes_addr (a := (s - 96 + 56).toNat + 4 + 8) (b := s.toNat - 28) (by omega) $$ V68
  ihave V60 := join64' (a := s.toNat - 36) (b := s.toNat - 32) p _ (by omega) $$ [V60 V64]
  · iframe V60 V64
  mstep; mstep [V60]
  rw [ofNat_decode_pair]
  mstep
  icases split64' (a := s.toNat - 36) (b := s.toNat - 32) p _ (by omega) $$ V60 with ⟨V60, V64⟩
  mstep; mstep; mstep
  mstep; mstep [V56]; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep [V68]; mstep [F24]
  mstep; mstep; mstep [F16]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep
  ihave V64 := join64' (a := s.toNat - 32) (b := s.toNat - 28) _ _ (by omega) $$ [V64 V68]
  · iframe V64 V68
  ihave Lo := stkA (show (s - 96).toNat - 160 = s.toNat - 256 by omega) $$ Lo
  icases stkSp 112 48 rfl $$ Lo with ⟨LoA, LoB⟩
  mcall (f372_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 96) (s - 96 + 56) r
      (q + 4 + UInt32.ofNat pre.length) (m - 4 - UInt32.ofNat pre.length) (bytes32 0)
      (bytes32 (UInt32.ofNat pre.length) ++ bytes32 (UInt32.ofNat pre.length)) f72 (bytes32 x0 ++ bytes32 x1)
      (bytes32 y0 ++ bytes32 y1) (by simp) (by simp) hf72 (by simp) (by simp) (by omega) (by rw [hm1]; omega)
      (by rw [hq1]; omega) (by omega) hr)
    using [Hg LoB Hr V56 V64 F72 B0 B1]
  · iunfold pre372
    ihave LoB := stkA (show s.toNat - 256 + 112 = (s - 96).toNat - 48 by omega) $$ LoB
    ihave V56 := memBytes_addr (show s.toNat - 40 = (s - 96 + 56).toNat by omega) $$ V56
    ihave V64 := memBytes_addr (a := s.toNat - 32) (b := (s - 96 + 56).toNat + 8) (by omega) $$ V64
    ihave F72 := memBytes_addr (show s.toNat - 24 = (s - 96 + 56).toNat + 16 by omega) $$ F72
    ihave B0 := memBytes_addr (a := q.toNat + 4 + pre.length) (b := (q + 4 + UInt32.ofNat pre.length).toNat) (by omega) $$ B0
    ihave B1 := memBytes_addr (a := q.toNat + 4 + pre.length + 8) (b := (q + 4 + UInt32.ofNat pre.length).toNat + 8) (by omega) $$ B1
    iframe Hg LoB Hr V56 V64 F72 B0 B1
    ipureintro; rfl
  iunfold post372 at HQ
  icases HQ with ⟨%hrs, Hg, LoB, Hr, V56, Q8, Q16, B0, B1⟩
  subst hrs
  ihave Q8 := memBytes_addr (a := (s - 96 + 56).toNat + 8) (b := s.toNat - 32) (by omega) $$ Q8
  ihave Q16 := memBytes_addr (a := (s - 96 + 56).toNat + 16) (b := s.toNat - 24) (by omega) $$ Q16
  icases split64' (a := s.toNat - 32) (b := s.toNat - 28) x0 x1 (by omega) $$ Q8 with ⟨X0, X1⟩
  icases split64' (a := s.toNat - 24) (b := s.toNat - 20) y0 y1 (by omega) $$ Q16 with ⟨Y0, Y1⟩
  -- [40, 48) := [68, 76)
  ihave X1 := join64' (a := s.toNat - 28) (b := s.toNat - 24) x1 y0 (by omega) $$ [X1 Y0]
  · iframe X1 Y0
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [X1]
  rw [ofNat_decode_pair]
  mstep [F40]
  rw [storeBytes_pair64]
  icases split64' (a := s.toNat - 28) (b := s.toNat - 24) x1 y0 (by omega) $$ X1 with ⟨X1, Y0⟩
  icases split64' (a := s.toNat - 56) (b := s.toNat - 52) x1 y0 (by omega) $$ F40 with ⟨F40, F44⟩
  -- [48] := [76]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [Y1]; mstep [F48]
  -- [32, 40) := [60, 68)
  ihave V60 := join64' (a := s.toNat - 36) (b := s.toNat - 32) p x0 (by omega) $$ [V60 X0]
  · iframe V60 X0
  mstep; mstep; mstep [V60]
  rw [ofNat_decode_pair]
  mstep [F32]
  rw [storeBytes_pair64]
  icases split64' (a := s.toNat - 36) (b := s.toNat - 32) p x0 (by omega) $$ V60 with ⟨V60, X0⟩
  icases split64' (a := s.toNat - 64) (b := s.toNat - 60) p x0 (by omega) $$ F32 with ⟨F32, F36⟩
  mstep; mstep [V56]; mstep; mstep; mstep
  -- hi := [44, 52)
  ihave F44 := join64' (a := s.toNat - 52) (b := s.toNat - 48) y0 y1 (by omega) $$ [F44 F48]
  · iframe F44 F48
  mstep; mstep; mstep; mstep; mstep; mstep [F44]
  rw [ofNat_decode_pair]
  mstep
  -- lo := [36, 44)
  ihave F36 := join64' (a := s.toNat - 60) (b := s.toNat - 56) x0 x1 (by omega) $$ [F36 F40]
  · iframe F36 F40
  mstep; mstep [F36]
  rw [ofNat_decode_pair]
  mstep
  mstep; mstep; mstep; mstep
  ihave X0 := join64' (a := s.toNat - 32) (b := s.toNat - 28) x0 x1 (by omega) $$ [X0 X1]
  · iframe X0 X1
  mcall (f371_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 96) (s - 96 + 56) r
      (q + 4 + UInt32.ofNat pre.length + 16) (m - 4 - UInt32.ofNat pre.length - 16) (bytes32 0)
      (bytes32 x0 ++ bytes32 x1) (bytes32 z0 ++ bytes32 z1) (by simp) (by simp) (by simp) (by omega)
      (by rw [hm2]; omega) (by rw [hq2]; omega) (by omega) hr)
    using [Hg LoB Hr V56 X0 C0]
  · iunfold pre371
    ihave X0 := memBytes_addr (a := s.toNat - 32) (b := (s - 96 + 56).toNat + 8) (by omega) $$ X0
    ihave C0 := memBytes_addr (a := q.toNat + 4 + pre.length + 16) (b := (q + 4 + UInt32.ofNat pre.length + 16).toNat) (by omega) $$ C0
    iframe Hg LoB Hr V56 X0 C0
    ipureintro; rfl
  iunfold post371 at HQ
  icases HQ with ⟨%hrs, Hg, LoB, Hr, V56, Q8, C0⟩
  subst hrs
  ihave Q8 := memBytes_addr (a := (s - 96 + 56).toNat + 8) (b := s.toNat - 32) (by omega) $$ Q8
  icases split64' (a := s.toNat - 32) (b := s.toNat - 28) z0 z1 (by omega) $$ Q8 with ⟨Z0, Z1⟩
  -- [88] := [68]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [Z1]; mstep [F88]
  -- [80, 88) := [60, 68)
  ihave V60 := join64' (a := s.toNat - 36) (b := s.toNat - 32) p z0 (by omega) $$ [V60 Z0]
  · iframe V60 Z0
  mstep; mstep; mstep [V60]
  rw [ofNat_decode_pair]
  mstep [F80]
  rw [storeBytes_pair64]
  icases split64' (a := s.toNat - 36) (b := s.toNat - 32) p z0 (by omega) $$ V60 with ⟨V60, Z0⟩
  icases split64' (a := s.toNat - 16) (b := s.toNat - 12) p z0 (by omega) $$ F80 with ⟨F80, F84⟩
  mstep; mstep; mstep [V56]; mstep; mstep; mstep
  -- [8] := [24]; [0, 8) := [16, 24)
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [F24]; mstep; mstep [F8]
  mstep; mstep; mstep [F16]
  rw [ofNat_decode_pair]
  mstep; mstep [F0]
  rw [storeBytes_pair64]
  -- v := [84, 92)
  ihave F84 := join64' (a := s.toNat - 12) (b := s.toNat - 8) z0 z1 (by omega) $$ [F84 F88]
  · iframe F84 F88
  mstep; mstep [F84]
  rw [ofNat_decode_pair]
  mstep
  mstep; mstep; mstep; mstep; mstep [Ho16]
  mstep; mstep; mstep; mstep; mstep [Ho8]
  mstep; mstep; mstep; mstep; mstep [Ho24]
  mstep; mstep; mstep; mstep; mstep [Ho32]
  mstep; mstep; mstep; mstep; mstep [Ho40]
  mstep; mstep; mstep [Ho0]
  simp only [storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep [Hg]
  rw [show s - 96 + 96 = s by simp]
  mcredits R
  ihave B0 := memBytes_addr (b := q.toNat + 4 + pre.length) (a := (q + 4 + UInt32.ofNat pre.length).toNat) (by omega) $$ B0
  ihave B1 := memBytes_addr (b := q.toNat + 4 + pre.length + 8) (a := (q + 4 + UInt32.ofNat pre.length).toNat + 8) (by omega) $$ B1
  ihave C0 := memBytes_addr (b := q.toNat + 4 + pre.length + 16) (a := (q + 4 + UInt32.ofNat pre.length + 16).toNat) (by omega) $$ C0
  ihave J := joinB (a := out.toNat + 8) (b := out.toNat + 16) (bytes32 x0 ++ bytes32 x1) _ (by simp) $$ [Ho8 Ho16]
  · iframe Ho8 Ho16
  ihave J := joinB (a := out.toNat + 8) (b := out.toNat + 24) ((bytes32 x0 ++ bytes32 x1) ++ (bytes32 y0 ++ bytes32 y1)) _ (by simp) $$ [J Ho24]
  · iframe J Ho24
  ihave J := joinB (a := out.toNat + 8) (b := out.toNat + 32) (((bytes32 x0 ++ bytes32 x1) ++ (bytes32 y0 ++ bytes32 y1)) ++ (bytes32 z0 ++ bytes32 z1)) _ (by simp) $$ [J Ho32]
  · iframe J Ho32
  ihave J := joinB (a := out.toNat + 8) (b := out.toNat + 40) ((((bytes32 x0 ++ bytes32 x1) ++ (bytes32 y0 ++ bytes32 y1)) ++ (bytes32 z0 ++ bytes32 z1)) ++ (bytes32 p ++ bytes32 (UInt32.ofNat pre.length))) _ (by simp) $$ [J Ho40]
  · iframe J Ho40
  ihave HW : heapWith n maxP len live p pre $$ [Hinv Hb]
  · iunfold heapWith
    iexists len'
    iframe Hinv Hb
    ipureintro; exact hl'
  -- the stack
  ihave F0 := stkB (a := s.toNat - 96) (b := s.toNat - 96) (k := 8) _ rfl (by simp) $$ F0
  ihave F8 := stkW (a := s.toNat - 88) (b := s.toNat - 88) _ rfl $$ F8
  ihave F16 := stkB (a := s.toNat - 80) (b := s.toNat - 80) (k := 8) _ rfl (by simp) $$ F16
  ihave F24 := stkW (a := s.toNat - 72) (b := s.toNat - 72) _ rfl $$ F24
  ihave F32 := stkW (a := s.toNat - 64) (b := s.toNat - 64) _ rfl $$ F32
  ihave F36 := stkB (a := s.toNat - 60) (b := s.toNat - 60) (k := 8) _ rfl (by simp) $$ F36
  ihave F44 := stkB (a := s.toNat - 52) (b := s.toNat - 52) (k := 8) _ rfl (by simp) $$ F44
  ihave V56 := stkW (a := (s - 96 + 56).toNat) (b := s.toNat - 40) _ (by omega) $$ V56
  ihave V60 := stkW (a := s.toNat - 36) (b := s.toNat - 36) _ rfl $$ V60
  ihave Z0 := stkW (a := s.toNat - 32) (b := s.toNat - 32) _ rfl $$ Z0
  ihave Z1 := stkW (a := s.toNat - 28) (b := s.toNat - 28) _ rfl $$ Z1
  ihave Y0 := stkW (a := s.toNat - 24) (b := s.toNat - 24) _ rfl $$ Y0
  ihave Y1 := stkW (a := s.toNat - 20) (b := s.toNat - 20) _ rfl $$ Y1
  ihave F80 := stkW (a := s.toNat - 16) (b := s.toNat - 16) _ rfl $$ F80
  ihave F84 := stkB (a := s.toNat - 12) (b := s.toNat - 12) (k := 8) _ rfl (by simp) $$ F84
  ihave F84 := stkJ (a := s.toNat - 12) (b := s.toNat - 4) (k1 := 8) (k2 := 4) (k := 12) (by omega) rfl $$ [F84 F92]
  · iframe F84 F92
  ihave F80 := stkJ (a := s.toNat - 16) (b := s.toNat - 12) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [F80 F84]
  · iframe F80 F84
  ihave Y1 := stkJ (a := s.toNat - 20) (b := s.toNat - 16) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [Y1 F80]
  · iframe Y1 F80
  ihave Y0 := stkJ (a := s.toNat - 24) (b := s.toNat - 20) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [Y0 Y1]
  · iframe Y0 Y1
  ihave Z1 := stkJ (a := s.toNat - 28) (b := s.toNat - 24) (k1 := 4) (k2 := 24) (k := 28) (by omega) rfl $$ [Z1 Y0]
  · iframe Z1 Y0
  ihave Z0 := stkJ (a := s.toNat - 32) (b := s.toNat - 28) (k1 := 4) (k2 := 28) (k := 32) (by omega) rfl $$ [Z0 Z1]
  · iframe Z0 Z1
  ihave V60 := stkJ (a := s.toNat - 36) (b := s.toNat - 32) (k1 := 4) (k2 := 32) (k := 36) (by omega) rfl $$ [V60 Z0]
  · iframe V60 Z0
  ihave V56 := stkJ (a := s.toNat - 40) (b := s.toNat - 36) (k1 := 4) (k2 := 36) (k := 40) (by omega) rfl $$ [V56 V60]
  · iframe V56 V60
  ihave F52 := stkJ (a := s.toNat - 44) (b := s.toNat - 40) (k1 := 4) (k2 := 40) (k := 44) (by omega) rfl $$ [F52 V56]
  · iframe F52 V56
  ihave F44 := stkJ (a := s.toNat - 52) (b := s.toNat - 44) (k1 := 8) (k2 := 44) (k := 52) (by omega) rfl $$ [F44 F52]
  · iframe F44 F52
  ihave F36 := stkJ (a := s.toNat - 60) (b := s.toNat - 52) (k1 := 8) (k2 := 52) (k := 60) (by omega) rfl $$ [F36 F44]
  · iframe F36 F44
  ihave F32 := stkJ (a := s.toNat - 64) (b := s.toNat - 60) (k1 := 4) (k2 := 60) (k := 64) (by omega) rfl $$ [F32 F36]
  · iframe F32 F36
  ihave F28 := stkJ (a := s.toNat - 68) (b := s.toNat - 64) (k1 := 4) (k2 := 64) (k := 68) (by omega) rfl $$ [F28 F32]
  · iframe F28 F32
  ihave F24 := stkJ (a := s.toNat - 72) (b := s.toNat - 68) (k1 := 4) (k2 := 68) (k := 72) (by omega) rfl $$ [F24 F28]
  · iframe F24 F28
  ihave F16 := stkJ (a := s.toNat - 80) (b := s.toNat - 72) (k1 := 8) (k2 := 72) (k := 80) (by omega) rfl $$ [F16 F24]
  · iframe F16 F24
  ihave F12 := stkJ (a := s.toNat - 84) (b := s.toNat - 80) (k1 := 4) (k2 := 80) (k := 84) (by omega) rfl $$ [F12 F16]
  · iframe F12 F16
  ihave F8 := stkJ (a := s.toNat - 88) (b := s.toNat - 84) (k1 := 4) (k2 := 84) (k := 88) (by omega) rfl $$ [F8 F12]
  · iframe F8 F12
  ihave F0 := stkJ (a := s.toNat - 96) (b := s.toNat - 88) (k1 := 8) (k2 := 88) (k := 96) (by omega) rfl $$ [F0 F8]
  · iframe F0 F8
  ihave LoB := stkA (b := s.toNat - 144) (by omega) $$ LoB
  ihave LoB := stkJ (a := s.toNat - 144) (b := s.toNat - 96) (k1 := 48) (k2 := 96) (k := 144) (by omega) rfl $$ [LoB F0]
  · iframe LoB F0
  ihave Stk := stkJ (a := s.toNat - 256) (b := s.toNat - 144) (k1 := 112) (k2 := 144) (k := 256) (by omega) rfl $$ [LoA LoB]
  · iframe LoA LoB
  iframe Hc
  iunfold post425
  iframe Hg Stk Hvt Hr Ho0 Hd4 Hpre B0 B1 C0
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe HW
  simp only [ftHead, List.append_assoc]
  iexact J

end Spec

end WNear.Binary.BorshFT
