import Bridge.Functions.FmtSink
import Bridge.Functions.MemCpy
import Binary.Code.Part15

/-!
# `str::repeat` (function 847) as `Contract::new` calls it

`<[u8]>::repeat(out, ptr, len, n)`:

```
847  sp -= 32
     n = 0 ⇒ the empty Vec (not taken)
     cap = n · len (i64; overflow ⇒ 879, negative ⇒ 844: not taken)
     p = __rust_alloc(cap, 1) (310)            (p = 0 ⇒ 842: not taken)
     cap < len ⇒ reserve (845)                 (not taken: cap ≥ len)
     memcpy(p, ptr, len) (951); m = len; k = n >> 1
     loop: memcpy(p + m, p, m); m <<= 1; k >>= 1; while k ≠ 0
     r = cap - m; r ≠ 0 ⇒ memcpy(p + m, p, r)  (not taken: r = 0)
     out ← (p, cap, cap); sp += 32
```

`f847_spec`: `measure_account_storage_usage`'s `"a".repeat(64)` (`ptr = 1052792`, the byte
`97`, `len = 1`, `n = 64`): `out` holds `(p, 64, 64)`, the block `p` holds 64 bytes `97` and is
live in the heap invariant (`grown`). The loop doubles six times (`m = 1, 2, …, 32`), proved
with `mwpi_loop` from the invariant `inv` (iteration `i`: `m = 2^i`, `k = 32 >>> i`, the first
`2^i` bytes copied).
-/

namespace WNear.Binary.StrRepeat

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word roomFor grownLen stk_addr stk_open581
  stk_close581)
open WNear.Binary.VecWithCap (vecCode2 okG costAllocF f310_roomG)
open WNear.Binary.FmtSink (grown heapInv_bound)

/-! ## The loop's arithmetic -/

/-- The cost of the iteration copying `2^i` bytes, the `memcpy` included. -/
def it (c₀ i : Nat) : Nat := 27 * c₀ + MemCpy.cost (2 ^ i) * c₀

/-- The cost of the last `k` iterations. -/
def left (c₀ : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => it c₀ (5 - k) + left c₀ k

theorem left_succ (c₀ i : Nat) (h : i < 6) : left c₀ (6 - i) = it c₀ i + left c₀ (6 - (i + 1)) := by
  rw [show 6 - i = (5 - i) + 1 by omega, left, show 5 - (5 - i) = i by omega, show 6 - (i + 1) = 5 - i by omega]

theorem left6 (c₀ : Nat) : left c₀ 6 = 1332 * c₀ := by
  simp only [left, it, MemCpy.cost]; norm_num; omega

theorem pow_toNat (i : Nat) (h : i < 6) : (UInt32.ofNat (2 ^ i)).toNat = 2 ^ i := by
  interval_cases i <;> rfl

theorem pow_le (i : Nat) (h : i < 6) : 2 ^ i ≤ 32 := by
  interval_cases i <;> decide

theorem pow_shl (i : Nat) (h : i < 6) : UInt32.ofNat (2 ^ i) <<< (1 % 32) = UInt32.ofNat (2 ^ (i + 1)) := by
  interval_cases i <;> decide

theorem pow_shr (i : Nat) (h : i < 5) : UInt32.ofNat (2 ^ (5 - i)) >>> (1 % 32) = UInt32.ofNat (2 ^ (5 - (i + 1))) := by
  interval_cases i <;> decide

theorem pow_shr_ne (i : Nat) (h : i < 5) : UInt32.ofNat (2 ^ (5 - i)) >>> (1 % 32) ≠ 0 := by
  interval_cases i <;> decide

theorem pow_shr5 : UInt32.ofNat (2 ^ (5 - 5)) >>> (1 % 32) = 0 := by decide

theorem rep_double (m : Nat) : List.replicate m (97 : UInt8) ++ List.replicate m 97 = List.replicate (2 * m) 97 := by
  rw [List.replicate_append_replicate]; congr 1; omega

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- What the loop does not touch: the frame, the stack, `out`, the source byte, the heap. -/
def fr847 (n g : Nat) (gt : GlobalType) (s out p : UInt32) (ob : List UInt8) (idx : UInt32)
    (ta a578 maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 (s - 32)⟩ ∗ stk n (s.toNat - 48) 48 ∗ n ↦[wms][ out.toNat ] ob ∗
    n ↦[wms][ 1052792 ] [97] ∗ vt n 1057464 idx ta a578 ∗ grown n maxP len live F p 64)

/-- The loop invariant at iteration `i < 6`: `m = 2^i` bytes copied, `k = 2^(5 - i)`, the
credits of the iterations left. -/
def inv (n inst : Nat) (mi : ModuleInst) (Cg R c₀ : Nat) (out p s' : UInt32) (Fr : IProp GF) :
    List Value → Frame → IProp GF := fun X f =>
  iprop(∃ (i : Nat) (rest : List UInt8), ⌜X = [] ∧ i < 6 ∧ rest.length = 64 - 2 ^ i ∧
      f = ⟨#[.i32 out, .i32 p, .i32 (UInt32.ofNat (2 ^ i)), .i32 (UInt32.ofNat (2 ^ (5 - i))), .i32 s',
        .i32 p, .i32 64, .i32 64, .i64 64, .i32 0], inst, mi⟩⌝ ∗
    credits Cg (left c₀ (6 - i) + R) ∗ n ↦[wms][ p.toNat ] (List.replicate (2 ^ i) 97 ++ rest) ∗ Fr)

/-- Before `"a".repeat(64)`: the stack pointer `s`, the 48 bytes below it (847's frame of 32, the
allocator's 16 below), the 12 bytes of `out`, the byte `97` of `"a"`, the heap. -/
def pre847 (n g : Nat) (gt : GlobalType) (s out : UInt32) (ob : List UInt8) (idx : UInt32)
    (ta a578 maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 1052792, .i32 1, .i32 64]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 48) 48 ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ 1052792 ] [97] ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F)

/-- After: the `String` `(p, 64, 64)` at `out`, the block `p` (64 bytes `97`) live in the heap. -/
def post847 (n g : Nat) (gt : GlobalType) (s out : UInt32) (idx : UInt32)
    (ta a578 maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1052792 ] [97] ∗
    vt n 1057464 idx ta a578 ∗
    ∃ p : UInt32, ⌜p ≠ 0 ∧ p.toNat + 64 < 2 ^ 32⌝ ∗ n ↦[i32][ out.toNat ] p ∗
      n ↦[i32][ out.toNat + 4 ] 64 ∗ n ↦[i32][ out.toNat + 8 ] 64 ∗
      n ↦[wms][ p.toNat ] List.replicate 64 97 ∗ grown n maxP len live F p 64)

/-- The cost of `"a".repeat(64)` (847), activation excluded: 252 instructions, the allocation, and the
seven `memcpy`s (1 byte from the source, then 1, 2, 4, 8, 16, 32 bytes within the block). -/
def cost847 (cfg : WasmConfig) (F : Nat) : Nat :=
  252 * cfg.regularOpCost + costAllocF cfg F 64 +
    (MemCpy.cost 1 + (MemCpy.cost 1 + MemCpy.cost 2 + MemCpy.cost 4 + MemCpy.cost 8 + MemCpy.cost 16 +
      MemCpy.cost 32)) * cfg.regularOpCost

theorem cost847_eq (cfg : WasmConfig) (F : Nat) :
    cost847 cfg F = 1446 * cfg.regularOpCost + costAllocF cfg F 64 := by
  simp only [cost847, MemCpy.cost]; norm_num; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`"a".repeat(64)`** (847, `<[u8]>::repeat(out, 1052792, 1, 64)`), on `heapInv … F` (`F ≥ 1`): one
allocation of 64 bytes (`__rust_alloc`, 310, `grown`), the byte copied, then doubled six times. -/
theorem f847_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s out : UInt32) (ob : List UInt8) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (F : Nat) (hF : okG F) (hs : 48 ≤ s.toNat) (hob : ob.length = 12)
    (hr : roomFor len maxP 64) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f847 Cg
        (pre847 n g gt s out ob idx ta (A 578) maxP len live F)
        (fun _ => cost847 cfg F)
        (post847 n g gt s out idx ta (A 578) maxP len live F) := by
  iintro #Hv
  iunfold vecCode2 at Hv
  icases Hv with ⟨#Hcode, #H581, #H952, #H153, #H239, #H313, #H236, #H310, -, -, -, -, -, -, -, #H951, #H575⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold allocCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha310 := hm.funcs 310 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  rw [show (fun _ : List Value => cost847 cfg F) = (fun _ => 1446 * cfg.regularOpCost + costAllocF cfg F 64)
    from funext fun _ => cost847_eq cfg F]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre847 at HP
  icases HP with ⟨%hargs, Hg, Hs, Ho, Ha, Hvt, Hinv⟩
  subst hargs
  icases stk_split n (s.toNat - 48) 16 32 $$ Hs with ⟨Hs16, Hs32⟩
  ihave Hs16 := stk_addr (show s.toNat - 48 = (s - 32).toNat - 16 by omega) $$ Hs16
  icases stk_open581 n (s - 32) (by omega) $$ Hs16 with ⟨%o1, %o2, %o4, %⟨h1, h2, h4⟩, O1, O2, O4, W8⟩
  simp only [f847]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  simp only [show UInt32.toUInt64 1 * UInt32.toUInt64 64 = 64 from rfl, show (64 : UInt64).toUInt32 = 64 from rfl]
  mcall (f310_roomG cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32) 64 idx maxP
      len live F o1 o2 o4 (by omega) (by decide) (by decide) h1 h2 h4 hr hF) using [Hg O1 O2 O4 Hvt Hinv]
  · iframe Hg O1 O2 O4 Hvt Hinv
  icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %len', %hl', Hinv, Hb⟩
  subst hrs
  replace hl' : len' = len \/ len' = grownLen len 64 := hl'
  icases heapInv_bound (p := p.toNat) (s := (64 : UInt32).toNat) (by simp) $$ Hinv with ⟨%hpb, Hinv⟩
  simp only [UInt32.reduceToNat] at hpb
  iunfold block at Hb
  icases Hb with ⟨%bs, %hbs, Hb⟩
  icases U128From.memBytes_split n p.toNat 1 bs (by omega) $$ Hb with ⟨Hb1, Hb2⟩
  repeat mstep
  have S0 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg
      (MemCpy.pre n p 1052792 1 (bs.take 1) [97]) (fun _ => 24 * cfg.regularOpCost) (MemCpy.post n p 1052792 [97]) :=
    MemCpy.f951_spec cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg p 1052792 1 (bs.take 1) [97]
      (by simp; omega) rfl (by simp; omega) (by simp)
  mcall S0 using [Hb1 Ha]
  · iunfold MemCpy.pre
    simp only [UInt32.reduceToNat]
    iframe Hb1 Ha
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Hb1, Ha⟩
  subst hrs
  ihave Ha := memBytes_addr (show (1052792 : UInt32).toNat = 1052792 from rfl) $$ Ha
  repeat mstep
  -- the frame of the loop
  ihave Hs16 := stk_close581 n (s - 32) (by omega) $$ [HO W8]
  · iframe HO W8
  ihave Hs := stk_join n (s.toNat - 48) 16 32 $$ [Hs16 Hs32]
  · isplitl [Hs16]
    · iapply stk_addr (show (s - 32).toNat - 16 = s.toNat - 48 by omega) $$ Hs16
    · iexact Hs32
  ihave HF : fr847 n g gt s out p ob idx ta (A 578) maxP len live F $$ [Hg Hs Ho Ha Hvt Hinv]
  · iunfold fr847
    iframe Hg Hs Ho
    isplitl [Ha]; · iexact Ha
    iframe Hvt
    iunfold grown
    iexists len'
    simp only [UInt32.reduceToNat]
    iframe Hinv
    ipureintro; exact hl'
  ihave Hp := U128From.memBytes_join n p.toNat 1 [97] (bs.drop 1) rfl $$ [Hb1 Hb2]
  · iframe Hb1 Hb2
  have hl6 := left6 cfg.regularOpCost
  mcredits (cfg.regularOpCost + (left cfg.regularOpCost 6 + (21 * cfg.regularOpCost + R)))
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := left cfg.regularOpCost 6 + (21 * cfg.regularOpCost + R))
    (I := inv n inst mi Cg (21 * cfg.regularOpCost + R) cfg.regularOpCost out p (s - 32)
      (fr847 n g gt s out p ob idx ta (A 578) maxP len live F)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv at HI
    icases HI with ⟨%i, %rest, %⟨hX, hi, hrest, hgf⟩, Hc, Hp, HF⟩
    subst hX
    rw [hgf]
    clear hgf
    have hmi := pow_toNat i hi
    have hle := pow_le i hi
    have hpm : (p + UInt32.ofNat (2 ^ i)).toNat = p.toNat + 2 ^ i := by
      rw [UInt32.toNat_add, hmi]; omega
    rw [left_succ _ i hi]
    unfold it
    generalize hM : MemCpy.cost (2 ^ i) * cfg.regularOpCost = M
    ihave Hp := (memBytes_append (GF := GF) (H := NearState) n p.toNat (List.replicate (2 ^ i) 97) rest).1 $$ Hp
    icases Hp with ⟨Hs, Hd⟩
    simp only [List.length_replicate]
    ihave Hd := U128From.memBytes_split n (p.toNat + 2 ^ i) (2 ^ i) rest (by omega) $$ Hd
    icases Hd with ⟨Hd, Hr⟩
    ihave Hd := memBytes_addr (show p.toNat + 2 ^ i = (p + UInt32.ofNat (2 ^ i)).toNat by omega) $$ Hd
    have S : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg
        (MemCpy.pre n (p + UInt32.ofNat (2 ^ i)) p (UInt32.ofNat (2 ^ i)) (rest.take (2 ^ i))
          (List.replicate (2 ^ i) 97))
        (fun _ => M)
        (MemCpy.post n (p + UInt32.ofNat (2 ^ i)) p (List.replicate (2 ^ i) 97)) := by
      have := MemCpy.f951_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg
        (p + UInt32.ofNat (2 ^ i)) p (UInt32.ofNat (2 ^ i)) (rest.take (2 ^ i)) (List.replicate (2 ^ i) 97)
        (by simp [hmi]; omega) (by simp [hmi]) (by omega) (by omega)
      rw [hmi, hM] at this
      exact this
    mstep; mstep; mstep; mstep; mstep
    mcall S using [Hd Hs]
    · iunfold MemCpy.pre
      iframe Hd Hs
      ipureintro; rfl
    iunfold MemCpy.post at HQ
    icases HQ with ⟨%hrs, Hd, Hs⟩
    subst hrs
    ihave Hd := memBytes_addr (show (p + UInt32.ofNat (2 ^ i)).toNat =
      p.toNat + (List.replicate (2 ^ i) (97 : UInt8)).length by simp; omega) $$ Hd
    ihave Hp := (memBytes_append (GF := GF) (H := NearState) n p.toNat (List.replicate (2 ^ i) 97)
      (List.replicate (2 ^ i) 97)).2 $$ [Hs Hd]
    · iframe Hs Hd
    rw [rep_double]
    ihave Hr := memBytes_addr (show p.toNat + 2 ^ i + 2 ^ i = p.toNat + 2 * 2 ^ i by omega) $$ Hr
    ihave Hp := U128From.memBytes_join n p.toNat (2 * 2 ^ i) (List.replicate (2 * 2 ^ i) 97) (rest.drop (2 ^ i))
      (by simp) $$ [Hp Hr]
    · iframe Hp Hr
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    rw [pow_shl i hi]
    by_cases h5 : i < 5
    · ---------------------------------------------------------- back to the loop
      have hne := pow_shr_ne i h5
      mstep
      simp only [Post.mloop]
      mpay
      mcredits (left cfg.regularOpCost (6 - (i + 1)) + (21 * cfg.regularOpCost + R))
      iunfold inv
      iexists i + 1
      iexists rest.drop (2 ^ i)
      rw [show 2 * 2 ^ i = 2 ^ (i + 1) by rw [Nat.pow_succ, Nat.mul_comm]]
      iframe Hc HF Hp
      ipureintro
      refine ⟨rfl, by omega, ?_, ?_⟩
      · simp [hrest]; rw [Nat.pow_succ]; omega
      · rw [pow_shr i h5]
    · ---------------------------------------------------------- the last iteration
      obtain rfl : i = 5 := by omega
      rw [pow_shr5, show UInt32.ofNat (2 ^ (5 + 1)) = 64 from rfl]
      mstep
      iapply mwpi_br
      simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_zero, Post.mblock_br_succ]
      mpay
      iunfold fr847 at HF
      icases HF with ⟨Hg, Hs, Ho, Ha, Hvt, Hgr⟩
      icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
      icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O8⟩
      ihave O8 := memBytes_addr (show out.toNat + 4 + 4 = out.toNat + 8 by omega) $$ O8
      repeat mstep
      mstep [O8]; mstep; mstep; mstep [O4]; mstep; mstep; mstep [O0]; mstep; mstep; mstep
      rw [show s - 32 + 32 = s by simp]
      mstep [Hg]
      mcredits R
      have hd32 : rest.drop 32 = [] := List.drop_eq_nil_of_le (by rw [hrest]; decide)
      rw [hd32, List.append_nil]
      iframe Hc
      iunfold post847
      isplitr; · ipureintro; rfl
      iframe Hg Hs Ha Hvt
      iexists p
      iframe O0 O4 O8 Hgr Hp
      ipureintro; exact ⟨hp0, hpb⟩
  isplitl [Hc]
  · iexact Hc
  inext
  iintro Hc
  iunfold inv
  iexists 0
  iexists bs.drop 1
  rw [show List.replicate (2 ^ 0) (97 : UInt8) = [97] from rfl]
  iframe Hc HF Hp
  ipureintro
  refine ⟨rfl, by decide, by simp [hbs], ?_⟩
  rfl

end Spec

end WNear.Binary.StrRepeat

