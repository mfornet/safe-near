import Bridge.Functions.AllocZeroed

/-!
# `alloc::vec::from_elem::<u8>` (687) and the `RawVec` allocation below it

```wat
;; 684 Layout::array::<u8> (out, &(size, align)): align a power of two (else panic),
;;     out := ((size + align - 1) & -align, align)
;; 685 Layout::array (out, cap): [sp+8] := (cap, 1); 684(sp, sp + 8); out := [sp] (i64)
;; 689 alloc_impl (out, size, align, zeroed): size = 0 → ptr = align;
;;     else ptr = zeroed ? __rust_alloc_zeroed(size, align) : __rust_alloc(size, align);
;;     out := (ptr, size)
;; 688 / 690 Global::allocate / allocate_zeroed (out, size, align): 689 with zeroed 0 / 1
;; 686 RawVec::allocate_in (out, cap, init): the layout (685); size ≥ 2^31 → capacity_overflow;
;;     init ? 690 : 688; ptr = 0 → handle_alloc_error; out := (ptr, cap)
;; 681 Vec::with_capacity_in (out, cap): 686(sp + 8, cap, 0); out := ([sp+8] (i64), len 0)
;; 687 from_elem (out, elem, n): elem & 255 = 0 → 686(sp + 8, n, 1), out := ([sp+8], n);
;;     else 681(sp + 16, n); memset([sp+16], elem, n); out := ([sp+16], n)
```

Everything here is for `u8` (`align = 1`). The stack: each spec owns a region of the shadow
stack below `sp` (`stk n a k`, any contents) and gives it back.
-/

namespace WNear.Binary.VecFromElem

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocNewCell (cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.Interface (IfaceMod)

/-! ## Words and pairs -/

/-- Two words as one `u64` (`lo` first, little-endian). -/
def pair64 (lo hi : UInt32) : UInt64 := UInt64.ofNat (lo.toNat + 2 ^ 32 * hi.toNat)

theorem storeBytes_pair64 (lo hi : UInt32) :
    storeBytes (.i64 (pair64 lo hi)) 8 = bytes32 lo ++ bytes32 hi := by
  have h1 := lo.toNat_lt
  have h2 := hi.toNat_lt
  simp only [storeBytes, storeRaw, pair64, bytes32, List.range, List.range.loop, List.map,
    List.cons_append, List.nil_append, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat',
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (apply UInt8.toNat_inj.mp; simp <;> omega)

theorem load_pair64 (lo hi : UInt32) :
    loadValue .i64 none (Memory.decodeLE (bytes32 lo ++ bytes32 hi)) = .i64 (pair64 lo hi) := by
  rw [U128From.decodeLE_append, decodeLE_bytes32, decodeLE_bytes32, bytes32_length]
  simp [loadValue, pair64]

theorem ofNat_decode_pair (lo hi : UInt32) :
    UInt64.ofNat (Memory.decodeLE (bytes32 lo ++ bytes32 hi)) = pair64 lo hi := by
  rw [U128From.decodeLE_append, decodeLE_bytes32, decodeLE_bytes32, bytes32_length]
  simp [pair64]

theorem layout_size (c : UInt32) : (1 + c + 4294967295) &&& (0 - 1) = c := by
  rw [UInt32.add_comm 1 c, UInt32.add_assoc, show (1 : UInt32) + 4294967295 = 0 by decide, UInt32.add_zero,
    show (0 : UInt32) - 1 = 4294967295 by decide]
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_and]
  have := c.toNat_lt
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

section Stack

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `k` bytes at `a`, any contents: a piece of the shadow stack. -/
def stk (n a k : Nat) : IProp GF := iprop(∃ bs : List UInt8, ⌜bs.length = k⌝ ∗ n ↦[wms][ a ] bs)

theorem stk_split (n a k1 k2 : Nat) :
    stk (GF := GF) n a (k1 + k2) ⊢ stk n a k1 ∗ stk n (a + k1) k2 := by
  iintro H
  iunfold stk at H
  icases H with ⟨%bs, %hbs, H⟩
  iunfold stk
  ihave H := U128From.memBytes_split n a k1 bs (by omega) $$ H
  icases H with ⟨H1, H2⟩
  isplitl [H1]
  · iexists bs.take k1; iframe H1; ipureintro; simp; omega
  · iexists bs.drop k1; iframe H2; ipureintro; simp; omega

theorem stk_join (n a k1 k2 : Nat) :
    stk (GF := GF) n a k1 ∗ stk n (a + k1) k2 ⊢ stk n a (k1 + k2) := by
  iintro ⟨H1, H2⟩
  iunfold stk at H1 H2
  icases H1 with ⟨%b1, %hb1, H1⟩
  icases H2 with ⟨%b2, %hb2, H2⟩
  iunfold stk
  iexists b1 ++ b2
  isplitr
  · ipureintro; simp; omega
  iapply U128From.memBytes_join n a k1 b1 b2 hb1
  iframe H1 H2

theorem stk_intro (n a : Nat) (bs : List UInt8) :
    n ↦[wms][ a ] bs ⊢ stk (GF := GF) n a bs.length := by
  iintro H; iunfold stk; iexists bs; iframe H; ipureintro; rfl

end Stack

/-! ## `Layout::array::<u8>` (684) -/

section L684

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre684 (n g : Nat) (gt : GlobalType) (s out lp c : UInt32) (ob0 ob4 : List UInt8) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i32 lp]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ n ↦[i32][ lp.toNat ] c ∗
    n ↦[i32][ lp.toNat + 4 ] 1 ∗ n ↦[wms][ out.toNat ] ob0 ∗ n ↦[wms][ out.toNat + 4 ] ob4)

def post684 (n g : Nat) (gt : GlobalType) (s out lp c : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ n ↦[i32][ lp.toNat ] c ∗
    n ↦[i32][ lp.toNat + 4 ] 1 ∗ n ↦[i32][ out.toNat ] c ∗ n ↦[i32][ out.toNat + 4 ] 1)

/-- `Layout::array::<u8>` (684) on `(c, 1)`: the layout `(c, 1)` at `out`. -/
theorem f684_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (Cg : Nat)
    (gt : GlobalType) (s out lp c : UInt32) (ob0 ob4 : List UInt8)
    (hob0 : ob0.length = 4) (hob4 : ob4.length = 4) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f684 Cg (pre684 n g gt s out lp c ob0 ob4)
        (fun _ => 33 * cfg.regularOpCost) (post684 n g gt s out lp c) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre684 at HP
  icases HP with ⟨%hargs, Hg, Hc0, Hc4, Ho0, Ho4⟩
  subst hargs
  simp only [f684]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [Hc4]; mstep; mstep; mstep; mstep; mstep
  mstep; mstep [Hc0]; mstep
  mstep; mstep; mstep [Ho4]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  simp only [UInt32.reduceOfNat]
  rw [layout_size]
  mstep [Ho0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post684
  iframe Hg Hc0 Hc4 Ho0 Ho4
  ipureintro; simp [htype]

end L684

/-! ## `Layout::array` (685) -/

section L685

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)

theorem stk_word (n a : Nat) (w : UInt32) : n ↦[i32][ a ] w ⊢ stk (GF := GF) n a 4 := by
  iintro H; iunfold stk; iexists bytes32 w; iframe H; ipureintro; simp

theorem stk16 (n a : Nat) :
    stk (GF := GF) n a 16 ⊢ stk n a 4 ∗ stk n (a + 4) 4 ∗ stk n (a + 8) 4 ∗ stk n (a + 12) 4 := by
  iintro H
  icases stk_split n a 4 12 $$ H with ⟨H1, H⟩
  icases stk_split n (a + 4) 4 8 $$ H with ⟨H2, H⟩
  icases stk_split n (a + 4 + 4) 4 4 $$ H with ⟨H3, H4⟩
  rw [show a + 4 + 4 = a + 8 by omega, show a + 8 + 4 = a + 12 by omega]
  iframe H1 H2 H3 H4

theorem stk16_join (n a : Nat) :
    stk (GF := GF) n a 4 ∗ stk n (a + 4) 4 ∗ stk n (a + 8) 4 ∗ stk n (a + 12) 4 ⊢ stk n a 16 := by
  iintro ⟨H1, H2, H3, H4⟩
  rw [show a + 12 = a + 8 + 4 by omega]
  ihave H3 := stk_join n (a + 8) 4 4 $$ [H3 H4]
  · iframe H3 H4
  rw [show a + 8 = a + 4 + 4 by omega]
  ihave H2 := stk_join n (a + 4) 4 8 $$ [H2 H3]
  · iframe H2 H3
  iapply stk_join n a 4 12
  iframe H1 H2

def pre685 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (ob : List UInt8) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
    n ↦[wms][ out.toNat ] ob)

def post685 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
    n ↦[i32][ out.toNat ] c ∗ n ↦[i32][ out.toNat + 4 ] 1)

/-- `Layout::array::<u8>(cap)` (685): `(cap, 1)` at `out`. -/
theorem f685_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (ob : List UInt8) (hob : ob.length = 8)
    (hs : 16 ≤ s.toNat) :
    A 684 ↪[wf] FuncInst.wasm types[14]! inst f684 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f685 Cg (pre685 n g gt s out c ob)
        (fun _ => 67 * cfg.regularOpCost) (post685 n g gt s out c) := by
  iintro ⟨#H684, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha684 := hm.funcs 684 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 16 + 8 := by simp [UInt32.toNat_add, h16]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre685 at HP
  icases HP with ⟨%hargs, Hg, Hs, Ho⟩
  subst hargs
  icases stk16 n (s.toNat - 16) $$ Hs with ⟨W0, W4, W8, W12⟩
  iunfold stk at W0 W4 W8 W12
  icases W0 with ⟨%b0, %hb0, W0⟩
  icases W4 with ⟨%b4, %hb4, W4⟩
  icases W8 with ⟨%b8, %hb8, W8⟩
  icases W12 with ⟨%b12, %hb12, W12⟩
  simp only [f685]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [W12]
  mstep; mstep; mstep [W8]
  mstep; mstep; mstep; mstep
  mcall (f684_spec cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg Cg gt (s - 16) (s - 16)
      (s - 16 + 8) c b0 b4 hb0 hb4) using [Hg W0 W4 W8 W12]
  · iunfold pre684
    ihave W8 := memBytes_addr (show s.toNat - 16 + 8 = (s - 16 + 8).toNat by omega) $$ W8
    ihave W12 := memBytes_addr (show s.toNat - 16 + 12 = (s - 16 + 8).toNat + 4 by omega) $$ W12
    ihave W0 := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ W0
    ihave W4 := memBytes_addr (show s.toNat - 16 + 4 = (s - 16).toNat + 4 by omega) $$ W4
    iframe Hg W0 W4 W8 W12
    ipureintro; rfl
  iunfold post684 at HQ
  icases HQ with ⟨%hrs, Hg, W8, W12, W0, W4⟩
  subst hrs
  ihave W0 := KeyGet.join64 n (s - 16).toNat c 1 $$ [W0 W4]
  · iframe W0 W4
  mstep; mstep; mstep [W0]
  rw [ofNat_decode_pair]
  mstep [Ho]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  ihave W0 := KeyGet.split64 n (s - 16).toNat c 1 $$ W0
  icases W0 with ⟨W0, W4⟩
  ihave Ho := KeyGet.split64 n out.toNat c 1 $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  iunfold post685
  iframe Hg Ho0 Ho4
  isplitr
  · ipureintro; simp [htype]
  iapply stk16_join
  ihave W0 := stk_word n _ c $$ W0
  ihave W4 := stk_word n _ 1 $$ W4
  ihave W8 := stk_word n _ c $$ W8
  ihave W12 := stk_word n _ 1 $$ W12
  rw [h16, e8]
  iframe W0 W4 W8 W12

end L685

/-! ## The allocation (689) -/

section L689

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode cost153 cost581 zeroedPost f313_spec_room)

/-- Room for an allocation of `size` bytes (align 1) on a heap of length `len`, under the
limit `maxP`. -/
def roomFor (len maxP : Nat) (size : UInt32) : Prop :=
  len % 65536 = 0 ∧ 0 < len ∧ len + (cellPages (wordsOf size) 1).toNat * 65536 + 65536 ≤ 2 ^ 32 ∧
    (len + (cellPages (wordsOf size) 1).toNat * 65536) / 65536 ≤ maxP

/-- The memory length after the allocation's grow. -/
def grownLen (len : Nat) (size : UInt32) : Nat := len + (cellPages (wordsOf size) 1).toNat * 65536

/-- The block's contents: zeroed (`z`) or any. -/
def content (n : Nat) (z : Bool) (p size : Nat) : IProp GF :=
  if z then iprop(n ↦[wms][ p ] List.replicate size 0) else block n p size

/-- The heap after `alloc_impl(size, 1, z)`: `size = 0` returns the dangling pointer 1 and
leaves the heap; otherwise a block `p ≠ 0`, `(p, size)` live. -/
def heapAfter (n maxP len : Nat) (live : List (Nat × Nat)) (z : Bool) (size p : UInt32) : IProp GF :=
  iprop(∃ len', ⌜(size.toNat = 0 ∧ p = 1 ∧ len' = len) ∨
      (0 < size.toNat ∧ p ≠ 0 ∧ (len' = len ∨ len' = grownLen len size))⌝ ∗
    heapInv n maxP len' (if size.toNat = 0 then live else (p.toNat, size.toNat) :: live) 1 ∗
    content n z p.toNat size.toNat)

/-- The allocator's cost: `__rust_alloc_zeroed` or `__rust_alloc`. -/
def costAlloc (cfg : WasmConfig) (z : Bool) (size : UInt32) : Nat :=
  if z then 15 * cfg.regularOpCost + (14 * cfg.regularOpCost + cost153 cfg size 1)
  else 15 * cfg.regularOpCost + (15 * cfg.regularOpCost + cost581 cfg size 1)

/-- The code `from_elem` runs (persistent). -/
def vecCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(allocCode n maxP inst mi A ∗
    A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗ A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗
    A 153 ↪[wf] FuncInst.wasm types[15]! inst f153 ∗ A 239 ↪[wf] FuncInst.wasm types[13]! inst f239 ∗
    A 313 ↪[wf] FuncInst.wasm types[13]! inst f313 ∗ A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗
    A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗ A 684 ↪[wf] FuncInst.wasm types[14]! inst f684 ∗
    A 685 ↪[wf] FuncInst.wasm types[14]! inst f685 ∗ A 689 ↪[wf] FuncInst.wasm types[45]! inst f689 ∗
    A 688 ↪[wf] FuncInst.wasm types[31]! inst f688 ∗ A 690 ↪[wf] FuncInst.wasm types[31]! inst f690 ∗
    A 686 ↪[wf] FuncInst.wasm types[31]! inst f686 ∗ A 681 ↪[wf] FuncInst.wasm types[14]! inst f681 ∗
    A 687 ↪[wf] FuncInst.wasm types[31]! inst f687)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (vecCode (GF := GF) n maxP inst mi A) := by
  unfold vecCode; infer_instance

theorem f310_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8) (hsp : 16 ≤ sp.toNat)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4) (hr : roomFor len maxP size) :
    allocCode n maxP inst mi A ∗ A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗
      A 581 ↪[wf] FuncInst.wasm types[15]! inst f581
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 1))
        (fun _ => 15 * cfg.regularOpCost + (15 * cfg.regularOpCost + (910 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) 1).toNat)))
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % (1 : UInt32).toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) 1).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) 1 ∗ block n p.toNat size.toNat)) := by
  obtain ⟨hlen0, hlen1, hroom, hmax⟩ := hr
  iintro ⟨#Hc, #H236, #H581⟩
  iunfold allocCode at Hc
  icases Hc with ⟨#H0, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11⟩
  iapply (AllocSeq.f310_spec_room cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size 1 idx 0 maxP len live
    o1 o2 o4 hsp rfl (by decide) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax)
  iframe H0 H236 H581 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11

theorem memBytes_nil (n i : Nat) : ⊢ memBytes (H := NearState) (GF := GF) n i [] := by
  unfold WasmLogic.memBytes byteCells; iapply BigSepL.bigSepL_nil.2; iempintro

/-- 581's three stack words out of a 16-byte region below `sp`. -/
theorem stk_open581 (n : Nat) (s : UInt32) (hs : 16 ≤ s.toNat) :
    stk (GF := GF) n (s.toNat - 16) 16 ⊢ ∃ o1 o2 o4 : List UInt8, ⌜o1.length = 4 ∧ o2.length = 4 ∧ o4.length = 4⌝ ∗
      n ↦[wms][ s.toNat - 16 ] o1 ∗ n ↦[wms][ s.toNat - 12 ] o2 ∗ n ↦[wms][ s.toNat - 4 ] o4 ∗
      stk n (s.toNat - 8) 4 := by
  iintro H
  icases stk16 n (s.toNat - 16) $$ H with ⟨W0, W4, W8, W12⟩
  iunfold stk at W0 W4 W12
  icases W0 with ⟨%b0, %hb0, W0⟩
  icases W4 with ⟨%b4, %hb4, W4⟩
  icases W12 with ⟨%b12, %hb12, W12⟩
  iexists b0, b4, b12
  rw [show s.toNat - 16 + 4 = s.toNat - 12 by omega, show s.toNat - 16 + 8 = s.toNat - 8 by omega,
    show s.toNat - 16 + 12 = s.toNat - 4 by omega]
  iframe W0 W4 W8 W12
  ipureintro; exact ⟨hb0, hb4, hb12⟩

theorem stk_close581 (n : Nat) (s : UInt32) (hs : 16 ≤ s.toNat) :
    (∃ o1 o2 o4 : List UInt8, ⌜o1.length = 4 ∧ o2.length = 4 ∧ o4.length = 4⌝ ∗
      n ↦[wms][ s.toNat - 16 ] o1 ∗ n ↦[wms][ s.toNat - 12 ] o2 ∗ n ↦[wms][ s.toNat - 4 ] o4) ∗
      stk (GF := GF) n (s.toNat - 8) 4 ⊢ stk n (s.toNat - 16) 16 := by
  iintro ⟨⟨%o1, %o2, %o4, %⟨h1, h2, h4⟩, W0, W4, W12⟩, W8⟩
  iapply stk16_join
  rw [show s.toNat - 16 + 4 = s.toNat - 12 by omega, show s.toNat - 16 + 8 = s.toNat - 8 by omega,
    show s.toNat - 16 + 12 = s.toNat - 4 by omega]
  iframe W8
  isplitl [W0]
  · iunfold stk; iexists o1; iframe W0; ipureintro; exact h1
  isplitl [W4]
  · iunfold stk; iexists o2; iframe W4; ipureintro; exact h2
  · iunfold stk; iexists o4; iframe W12; ipureintro; exact h4

def pre689 (n g : Nat) (gt : GlobalType) (s out size : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 size, .i32 1, .i32 (if z then 1 else 0)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗
    n ↦[wms][ out.toNat ] ob)

def post689 (n g : Nat) (gt : GlobalType) (s out size : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size ∗ heapAfter n maxP len live z size p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `alloc_impl(size, 1, z)` (689): no allocation for `size = 0` (the pointer 1), else
`__rust_alloc_zeroed` (`z`) or `__rust_alloc`; `(ptr, size)` at `out`. -/
theorem f689_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size : UInt32) (z : Bool) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 8) (hs : 16 ≤ s.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size) :
    vecCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f689 Cg
        (pre689 n g gt s out size z idx ta (A 578) maxP len live ob)
        (fun _ => 27 * cfg.regularOpCost + costAlloc cfg z size)
        (post689 n g gt s out size z idx ta (A 578) maxP len live) := by
  iintro #Hv
  iunfold vecCode at Hv
  icases Hv with ⟨#Hcode, #H581, #H952, #H153, #H239, #H313, #H236, #H310, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold allocCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha310 := hm.funcs 310 (by decide)
  have ha313 := hm.funcs 313 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre689 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : (ob.drop 4).length = 4 := by simp; omega
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  simp only [f689]
  by_cases h0 : size.toNat = 0
  · ---------------------------------------------------------------- size 0
    have hz : size = 0 := UInt32.toNat_inj.mp (by simpa using h0)
    subst hz
    mstep; mstep; mstep; mstep
    mstep; mstep; mstep [Ho4]
    mstep; mstep; mstep [Ho0]
    mcredits R
    iframe Hc
    iunfold post689
    isplitr
    · ipureintro; simp [htype]
    iexists 1
    iframe Hg Hs Hvt Ho0 Ho4
    iunfold heapAfter
    iexists len
    simp only [UInt32.toNat_zero, ite_true, List.replicate_zero]
    iframe Hinv
    isplitr
    · ipureintro; simp
    iunfold content
    cases z
    · simp only [Bool.false_eq_true, ite_false]
      iunfold block
      iexists []
      isplitr; · ipureintro; rfl
      iapply memBytes_nil
    · simp only [ite_true, List.replicate_zero]
      iapply memBytes_nil
  · ---------------------------------------------------------------- an allocation
    have hpos : 0 < size.toNat := Nat.pos_of_ne_zero h0
    have hne : size ≠ 0 := fun e => h0 (by simp [e])
    have hroom := hr hpos
    icases stk_open581 n s hs $$ Hs with ⟨%o1, %o2, %o4, %⟨h1, h2, h4⟩, O1, O2, O4, W8⟩
    cases z
    · -------------------------------------------------------------- __rust_alloc
      simp only [Bool.false_eq_true, ite_false, costAlloc, cost581]
      mstep; mstep; mstep; mstep
      mstep; mstep; mstep; mstep
      mstep; mstep
      mcall (f310_room cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s size idx maxP
          len live o1 o2 o4 hs hpos hsize2 h1 h2 h4 hroom) using [Hg O1 O2 O4 Hvt Hinv]
      · iframe Hg O1 O2 O4 Hvt Hinv
      icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %len', %hl', Hinv, Hb⟩
      subst hrs
      mcredits (7 * cfg.regularOpCost + R)
      mstep; mstep; mstep; mstep [Ho4]
      mstep; mstep; mstep [Ho0]
      mcredits R
      iframe Hc
      iunfold post689
      isplitr
      · ipureintro; simp [htype]
      iexists p
      iframe Hg Hvt Ho0 Ho4
      isplitl [HO W8]
      · iapply stk_close581 n s hs
        iframe HO W8
      iunfold heapAfter
      iexists len'
      simp only [h0, ite_false]
      iframe Hinv
      isplitr
      · ipureintro; right; exact ⟨hpos, hp0, hl'⟩
      iunfold content
      simp only [Bool.false_eq_true, ite_false]
      iexact Hb
    · -------------------------------------------------------------- __rust_alloc_zeroed
      simp only [ite_true, costAlloc]
      mstep; mstep; mstep; mstep
      mstep; mstep; mstep; mstep
      mstep; mstep
      mcall (f313_spec_room cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s size 1
          idx 0 maxP len live o1 o2 o4 hs rfl (by decide) hpos hsize2 hroom.1 hroom.2.1 h1 h2 h4 hroom.2.2.1
          hroom.2.2.2) using [Hg O1 O2 O4 Hvt Hinv]
      · iframe Hg O1 O2 O4 Hvt Hinv
      iunfold zeroedPost at HQ
      icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %len', %hl', Hinv, Hb⟩
      subst hrs
      mcredits (8 * cfg.regularOpCost + R)
      mstep; mstep
      mstep
      mstep; mstep [Ho4]
      mstep; mstep; mstep [Ho0]
      mcredits R
      iframe Hc
      iunfold post689
      isplitr
      · ipureintro; simp [htype]
      iexists p
      iframe Hg Hvt Ho0 Ho4
      isplitl [HO W8]
      · iapply stk_close581 n s hs
        iframe HO W8
      iunfold heapAfter
      iexists len'
      simp only [h0, ite_false]
      iframe Hinv
      isplitr
      · ipureintro; right; exact ⟨hpos, hp0, hl'⟩
      iunfold content
      simp only [ite_true]
      iexact Hb

end L689

/-! ## `Global::allocate` (688) and `allocate_zeroed` (690) -/

section L68x

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)

theorem stk_addr {n a b k : Nat} (h : a = b) : stk (GF := GF) n a k ⊢ stk n b k := by
  subst h; exact .rfl

def pre68x (n g : Nat) (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 size, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 32) 32 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗
    n ↦[wms][ out.toNat ] ob)

def post68x (n g : Nat) (gt : GlobalType) (s out size : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 32) 32 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size ∗ heapAfter n maxP len live z size p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `Global::allocate_zeroed` (690): `alloc_impl(size, 1, true)` (689) into its frame, `(ptr, size)`
copied to `out`. -/
theorem f690_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 8) (hs : 32 ≤ s.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size) :
    vecCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f690 Cg
        (pre68x n g gt s out size idx ta (A 578) maxP len live ob)
        (fun _ => 35 * cfg.regularOpCost + (27 * cfg.regularOpCost + costAlloc cfg true size))
        (post68x n g gt s out size true idx ta (A 578) maxP len live) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H689 : A 689 ↪[wf] FuncInst.wasm types[45]! inst f689 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha689 := hm.funcs 689 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by simp [UInt32.toNat_add, h16]; omega
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : (ob.drop 4).length = 4 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre68x at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨X, Hs⟩
  icases stk_split n (s.toNat - 32 + 16) 8 8 $$ Hs with ⟨Y, Z⟩
  iunfold stk at Z
  icases Z with ⟨%zb, %hzb, Z⟩
  simp only [f690]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f689_spec cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16 + 8) size true idx maxP len live zb hzb (by omega) hsize2 hr) using [Hg X Hvt Hinv Z]
  · iunfold pre689
    ihave X := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 32 + 16 + 8 = (s - 16 + 8).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; simp
  iunfold post689 at HQ
  icases HQ with ⟨%hrs, %p, Hg, X, Hvt, Z0, Z4, HA⟩
  subst hrs
  mcredits (13 * cfg.regularOpCost + R)
  mstep; mstep; mstep [Z0]; mstep [Ho0]
  mstep; mstep; mstep [Z4]; mstep [Ho4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post68x
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt Ho0 Ho4 HA
  ihave X := stk_addr (show (s - 16).toNat - 16 = s.toNat - 32 by omega) $$ X
  ihave Z0 := stk_word n _ p $$ Z0
  ihave Z4 := stk_word n _ size $$ Z4
  rw [e8]
  ihave Z := stk_join n (s.toNat - 8) 4 4 $$ [Z0 Z4]
  · iframe Z0 Z4
  ihave Z := stk_addr (show s.toNat - 8 = s.toNat - 32 + 16 + 8 by omega) $$ Z
  ihave Y := stk_join n (s.toNat - 32 + 16) 8 8 $$ [Y Z]
  · iframe Y Z
  iapply stk_join n (s.toNat - 32) 16 16
  iframe X Y

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `Global::allocate` (688): `alloc_impl(size, 1, false)` (689) into its frame, `(ptr, size)`
copied to `out`. -/
theorem f688_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 8) (hs : 32 ≤ s.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size) :
    vecCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f688 Cg
        (pre68x n g gt s out size idx ta (A 578) maxP len live ob)
        (fun _ => 35 * cfg.regularOpCost + (27 * cfg.regularOpCost + costAlloc cfg false size))
        (post68x n g gt s out size false idx ta (A 578) maxP len live) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H689 : A 689 ↪[wf] FuncInst.wasm types[45]! inst f689 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha689 := hm.funcs 689 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by simp [UInt32.toNat_add, h16]; omega
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : (ob.drop 4).length = 4 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre68x at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨X, Hs⟩
  icases stk_split n (s.toNat - 32 + 16) 8 8 $$ Hs with ⟨Y, Z⟩
  iunfold stk at Z
  icases Z with ⟨%zb, %hzb, Z⟩
  simp only [f688]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (f689_spec cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16 + 8) size false idx maxP len live zb hzb (by omega) hsize2 hr) using [Hg X Hvt Hinv Z]
  · iunfold pre689
    ihave X := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 32 + 16 + 8 = (s - 16 + 8).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; simp
  iunfold post689 at HQ
  icases HQ with ⟨%hrs, %p, Hg, X, Hvt, Z0, Z4, HA⟩
  subst hrs
  mcredits (13 * cfg.regularOpCost + R)
  mstep; mstep; mstep [Z0]; mstep [Ho0]
  mstep; mstep; mstep [Z4]; mstep [Ho4]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post68x
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt Ho0 Ho4 HA
  ihave X := stk_addr (show (s - 16).toNat - 16 = s.toNat - 32 by omega) $$ X
  ihave Z0 := stk_word n _ p $$ Z0
  ihave Z4 := stk_word n _ size $$ Z4
  rw [e8]
  ihave Z := stk_join n (s.toNat - 8) 4 4 $$ [Z0 Z4]
  · iframe Z0 Z4
  ihave Z := stk_addr (show s.toNat - 8 = s.toNat - 32 + 16 + 8 by omega) $$ Z
  ihave Y := stk_join n (s.toNat - 32 + 16) 8 8 $$ [Y Z]
  · iframe Y Z
  iapply stk_join n (s.toNat - 32) 16 16
  iframe X Y

end L68x

/-! ## `RawVec::allocate_in` (686) -/

section L686

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)

theorem les_neg1 (c : UInt32) (h : c.toNat < 2 ^ 31) :
    Numeric.bool (Numeric.irelop32 IRelOp.le_s c 4294967295) = 0 := by
  have h' : c.toNat < 2147483648 := h
  simp [Numeric.irelop32, Numeric.bool, UInt32.toIntS, h']
  omega

theorem heapAfter_ne {n maxP len : Nat} {live : List (Nat × Nat)} {z : Bool} {size p : UInt32} :
    heapAfter (GF := GF) n maxP len live z size p ⊢ ⌜p ≠ 0⌝ ∗ heapAfter n maxP len live z size p := by
  iintro H
  iunfold heapAfter at H
  icases H with ⟨%len', %h, H1, H2⟩
  isplitr
  · ipureintro
    rcases h with ⟨-, hp, -⟩ | ⟨-, hp, -⟩
    · rw [hp]; decide
    · exact hp
  iunfold heapAfter
  iexists len'
  iframe H1 H2
  ipureintro; exact h

/-- The 64 bytes below `sp` as 686 uses them. -/
theorem stk64 (n a : Nat) :
    stk (GF := GF) n a 64 ⊢ stk n a 16 ∗ stk n (a + 16) 16 ∗ stk n (a + 32) 8 ∗ stk n (a + 40) 8 ∗
      stk n (a + 48) 8 ∗ stk n (a + 56) 8 := by
  iintro H
  icases stk_split n a 16 48 $$ H with ⟨H1, H⟩
  icases stk_split n (a + 16) 16 32 $$ H with ⟨H2, H⟩
  icases stk_split n (a + 16 + 16) 8 24 $$ H with ⟨H3, H⟩
  icases stk_split n (a + 16 + 16 + 8) 8 16 $$ H with ⟨H4, H⟩
  icases stk_split n (a + 16 + 16 + 8 + 8) 8 8 $$ H with ⟨H5, H6⟩
  rw [show a + 16 + 16 = a + 32 by omega, show a + 32 + 8 = a + 40 by omega,
    show a + 40 + 8 = a + 48 by omega, show a + 48 + 8 = a + 56 by omega]
  iframe H1 H2 H3 H4 H5 H6

theorem stk64_join (n a : Nat) :
    stk (GF := GF) n a 16 ∗ stk n (a + 16) 16 ∗ stk n (a + 32) 8 ∗ stk n (a + 40) 8 ∗
      stk n (a + 48) 8 ∗ stk n (a + 56) 8 ⊢ stk n a 64 := by
  iintro ⟨H1, H2, H3, H4, H5, H6⟩
  rw [show a + 56 = a + 48 + 8 by omega]
  ihave H5 := stk_join n (a + 48) 8 8 $$ [H5 H6]
  · iframe H5 H6
  rw [show a + 48 = a + 40 + 8 by omega]
  ihave H4 := stk_join n (a + 40) 8 16 $$ [H4 H5]
  · iframe H4 H5
  rw [show a + 40 = a + 32 + 8 by omega]
  ihave H3 := stk_join n (a + 32) 8 24 $$ [H3 H4]
  · iframe H3 H4
  rw [show a + 32 = a + 16 + 16 by omega]
  ihave H2 := stk_join n (a + 16) 16 32 $$ [H2 H3]
  · iframe H2 H3
  iapply stk_join n a 16 48
  iframe H1 H2

def pre686 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c, .i32 (if z then 1 else 0)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗
    n ↦[wms][ out.toNat ] ob)

def post686 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗ heapAfter n maxP len live z c p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `RawVec::<u8>::allocate_in(cap, init)` (686): `(ptr, cap)` at `out`, zeroed for `init`;
`cap < 2^28` (so no `capacity_overflow`), with room (so no `handle_alloc_error`). -/
theorem f686_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (z : Bool) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 8) (hs : 64 ≤ s.toNat)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c) :
    vecCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f686 Cg
        (pre686 n g gt s out c z idx ta (A 578) maxP len live ob)
        (fun _ => 203 * cfg.regularOpCost + costAlloc cfg z c)
        (post686 n g gt s out c z idx ta (A 578) maxP len live) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H685 : A 685 ↪[wf] FuncInst.wasm types[14]! inst f685 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H684 : A 684 ↪[wf] FuncInst.wasm types[14]! inst f684 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H690 : A 690 ↪[wf] FuncInst.wasm types[31]! inst f690 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H688 : A 688 ↪[wf] FuncInst.wasm types[31]! inst f688 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha685 := hm.funcs 685 (by decide)
  have ha688 := hm.funcs 688 (by decide)
  have ha690 := hm.funcs 690 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 32 + 8).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h32]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have e24 : (s - 32 + 24).toNat = s.toNat - 8 := by simp [UInt32.toNat_add, h32]; omega
  have hle := les_neg1 c (by omega)
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : (ob.drop 4).length = 4 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre686 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  icases stk64 n (s.toNat - 64) $$ Hs with ⟨R1, R2, U, Z8, Z16, L⟩
  iunfold stk at L
  icases L with ⟨%lb, %hlb, L⟩
  simp only [f686]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (f685_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 24) c lb hlb (by omega)) using [Hg R2 L]
  · iunfold pre685
    ihave R2 := stk_addr (show s.toNat - 64 + 16 = (s - 32).toNat - 16 by omega) $$ R2
    ihave L := memBytes_addr (show s.toNat - 64 + 56 = (s - 32 + 24).toNat by omega) $$ L
    iframe Hg R2 L
    ipureintro; rfl
  iunfold post685 at HQ
  icases HQ with ⟨%hrs, Hg, R2, L0, L4⟩
  subst hrs
  ihave R2 := stk_addr (show (s - 32).toNat - 16 = s.toNat - 64 + 16 by omega) $$ R2
  mstep; mstep; mstep; mstep [L4]; mstep; mstep; mstep
  mstep; mstep [L0]; mstep; mstep; mstep; mstep
  mstep; mstep
  cases z
  · -------------------------------------------------------------- init = false
    simp only [Bool.false_eq_true, ite_false]
    iunfold stk at Z16
    icases Z16 with ⟨%zb, %hzb, Z⟩
    mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep
    mcall (f688_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
        (s - 32 + 16) c idx maxP len live zb hzb (by omega) hc28 hr) using [Hg R1 R2 Hvt Hinv Z]
    · iunfold pre68x
      ihave R1 := stk_join n (s.toNat - 64) 16 16 $$ [R1 R2]
      · iframe R1 R2
      ihave R1 := stk_addr (show s.toNat - 64 = (s - 32).toNat - 32 by omega) $$ R1
      ihave Z := memBytes_addr (show s.toNat - 64 + 48 = (s - 32 + 16).toNat by omega) $$ Z
      iframe Hg R1 Hvt Hinv Z
      ipureintro; rfl
    iunfold post68x at HQ
    icases HQ with ⟨%hrs, %p, Hg, R1, Hvt, Z0, Z4, HA⟩
    subst hrs
    ihave HA := heapAfter_ne $$ HA
    icases HA with ⟨%hp0, HA⟩
    mcredits (22 * cfg.regularOpCost + R)
    mstep; mstep [Z4]; mstep; mstep; mstep [Z0]; mstep
    
    mstep; mstep; mstep
    mstep; mstep; mstep [Ho0]
    mstep; mstep; mstep [Ho4]
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 32 + 32 = s by simp]
    mstep
    mcredits R
    iframe Hc
    iunfold post686
    isplitr
    · ipureintro; simp [htype]
    iexists p
    iframe Hg Hvt Ho0 Ho4 HA
    ihave R1 := stk_addr (show (s - 32).toNat - 32 = s.toNat - 64 by omega) $$ R1
    ihave R1 := stk_split n (s.toNat - 64) 16 16 $$ R1
    icases R1 with ⟨R1, R2⟩
    ihave Z0 := stk_word n _ p $$ Z0
    ihave Z4 := stk_word n _ c $$ Z4
    ihave Z := stk_join n _ 4 4 $$ [Z0 Z4]
    · iframe Z0 Z4
    ihave Z := stk_addr (show (s - 32 + 16).toNat = s.toNat - 64 + 48 by omega) $$ Z
    ihave L0 := stk_word n _ c $$ L0
    ihave L4 := stk_word n _ 1 $$ L4
    ihave L := stk_join n _ 4 4 $$ [L0 L4]
    · iframe L0 L4
    ihave L := stk_addr (show (s - 32 + 24).toNat = s.toNat - 64 + 56 by omega) $$ L
    iapply stk64_join
    iframe R1 R2 U Z8 Z
    iexact L
  · -------------------------------------------------------------- init = true
    simp only [ite_true]
    iunfold stk at Z8
    icases Z8 with ⟨%zb, %hzb, Z⟩
    mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep
    mcall (f690_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
        (s - 32 + 8) c idx maxP len live zb hzb (by omega) hc28 hr) using [Hg R1 R2 Hvt Hinv Z]
    · iunfold pre68x
      ihave R1 := stk_join n (s.toNat - 64) 16 16 $$ [R1 R2]
      · iframe R1 R2
      ihave R1 := stk_addr (show s.toNat - 64 = (s - 32).toNat - 32 by omega) $$ R1
      ihave Z := memBytes_addr (show s.toNat - 64 + 40 = (s - 32 + 8).toNat by omega) $$ Z
      iframe Hg R1 Hvt Hinv Z
      ipureintro; rfl
    iunfold post68x at HQ
    icases HQ with ⟨%hrs, %p, Hg, R1, Hvt, Z0, Z4, HA⟩
    subst hrs
    ihave HA := heapAfter_ne $$ HA
    icases HA with ⟨%hp0, HA⟩
    mcredits (23 * cfg.regularOpCost + R)
    mstep; mstep [Z4]; mstep; mstep; mstep [Z0]; mstep
    mstep
    mstep; mstep; mstep
    mstep; mstep; mstep [Ho0]
    mstep; mstep; mstep [Ho4]
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 32 + 32 = s by simp]
    mstep
    mcredits R
    iframe Hc
    iunfold post686
    isplitr
    · ipureintro; simp [htype]
    iexists p
    iframe Hg Hvt Ho0 Ho4 HA
    ihave R1 := stk_addr (show (s - 32).toNat - 32 = s.toNat - 64 by omega) $$ R1
    ihave R1 := stk_split n (s.toNat - 64) 16 16 $$ R1
    icases R1 with ⟨R1, R2⟩
    ihave Z0 := stk_word n _ p $$ Z0
    ihave Z4 := stk_word n _ c $$ Z4
    ihave Z := stk_join n _ 4 4 $$ [Z0 Z4]
    · iframe Z0 Z4
    ihave Z := stk_addr (show (s - 32 + 8).toNat = s.toNat - 64 + 40 by omega) $$ Z
    ihave L0 := stk_word n _ c $$ L0
    ihave L4 := stk_word n _ 1 $$ L4
    ihave L := stk_join n _ 4 4 $$ [L0 L4]
    · iframe L0 L4
    ihave L := stk_addr (show (s - 32 + 24).toNat = s.toNat - 64 + 56 by omega) $$ L
    iapply stk64_join
    iframe R1 R2 U Z Z16
    iexact L

end L686

/-! ## `Vec::with_capacity_in` (681) -/

section L681

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)

def pre681 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗
    n ↦[wms][ out.toNat ] ob)

def post681 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗ n ↦[i32][ out.toNat + 8 ] 0 ∗
    heapAfter n maxP len live false c p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `Vec::<u8>::with_capacity_in(cap)` (681): the `Vec` `(ptr, cap, 0)` at `out`. -/
theorem f681_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (hs : 80 ≤ s.toNat)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c) :
    vecCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f681 Cg
        (pre681 n g gt s out c idx ta (A 578) maxP len live ob)
        (fun _ => 35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAlloc cfg false c))
        (post681 n g gt s out c idx ta (A 578) maxP len live) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H686 : A 686 ↪[wf] FuncInst.wasm types[31]! inst f686 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha686 := hm.funcs 686 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by simp [UInt32.toNat_add, h16]; omega
  have hob0 : (ob.take 8).length = 8 := by simp; omega
  have hob4 : (ob.drop 8).length = 4 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre681 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho8⟩
  icases stk_split n (s.toNat - 80) 64 16 $$ Hs with ⟨X, Hs⟩
  icases stk_split n (s.toNat - 80 + 64) 8 8 $$ Hs with ⟨Y, Z⟩
  iunfold stk at Z
  icases Z with ⟨%zb, %hzb, Z⟩
  simp only [f681]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  mcall (f686_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16 + 8) c false idx maxP len live zb hzb (by omega) hc28 hr) using [Hg X Hvt Hinv Z]
  · iunfold pre686
    ihave X := stk_addr (show s.toNat - 80 = (s - 16).toNat - 64 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 80 + 64 + 8 = (s - 16 + 8).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; simp
  iunfold post686 at HQ
  icases HQ with ⟨%hrs, %p, Hg, X, Hvt, Z0, Z4, HA⟩
  subst hrs
  mcredits (13 * cfg.regularOpCost + R)
  ihave Z := KeyGet.join64 n (s - 16 + 8).toNat p c $$ [Z0 Z4]
  · iframe Z0 Z4
  mstep; mstep [Z]
  rw [ofNat_decode_pair]
  mstep
  mstep; mstep; mstep [Ho8]
  mstep; mstep; mstep [Ho0]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post681
  isplitr
  · ipureintro; simp [htype]
  iexists p
  ihave Ho0 := KeyGet.split64 n out.toNat p c $$ Ho0
  icases Ho0 with ⟨Ho0, Ho4⟩
  iframe Hg Hvt Ho0 Ho4 Ho8 HA
  ihave X := stk_addr (show (s - 16).toNat - 64 = s.toNat - 80 by omega) $$ X
  ihave Z := KeyGet.split64 n _ p c $$ Z
  icases Z with ⟨Z0, Z4⟩
  ihave Z0 := stk_word n _ p $$ Z0
  ihave Z4 := stk_word n _ c $$ Z4
  ihave Z := stk_join n _ 4 4 $$ [Z0 Z4]
  · iframe Z0 Z4
  ihave Z := stk_addr (show (s - 16 + 8).toNat = s.toNat - 80 + 64 + 8 by omega) $$ Z
  ihave Y := stk_join n (s.toNat - 80 + 64) 8 8 $$ [Y Z]
  · iframe Y Z
  iapply stk_join n (s.toNat - 80) 64 16
  iframe X Y

end L681

/-! ## `alloc::vec::from_elem::<u8>` (687) -/

section L687

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode heapInv_bound byteOf_zero)

theorem byteOf_and (e : UInt32) (h : e &&& 255 = 0) : MemSet.byteOf e = 0 := by
  have h2 := congrArg UInt32.toNat h
  simp [UInt32.toNat_and] at h2
  rw [show (255 : Nat) = 2 ^ 8 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod] at h2
  unfold MemSet.byteOf
  apply UInt8.toNat_inj.mp
  simp; omega

/-- The heap after `vec![b; size]`: `size = 0` leaves it (the pointer 1); otherwise a block
`p ≠ 0`, `(p, size)` live; the `size` bytes at `p` are `b`. -/
def vecAfter (n maxP len : Nat) (live : List (Nat × Nat)) (size p : UInt32) (b : UInt8) : IProp GF :=
  iprop(∃ len', ⌜(size.toNat = 0 ∧ p = 1 ∧ len' = len) ∨
      (0 < size.toNat ∧ p ≠ 0 ∧ (len' = len ∨ len' = grownLen len size))⌝ ∗
    heapInv n maxP len' (if size.toNat = 0 then live else (p.toNat, size.toNat) :: live) 1 ∗
    n ↦[wms][ p.toNat ] List.replicate size.toNat b)

theorem heapAfter_true {n maxP len : Nat} {live : List (Nat × Nat)} {size p : UInt32} :
    heapAfter (GF := GF) n maxP len live true size p ⊢ vecAfter n maxP len live size p 0 := by
  iintro H
  iunfold heapAfter, content at H
  icases H with ⟨%len', %h, H1, H2⟩
  iunfold vecAfter
  iexists len'
  simp only [ite_true]
  iframe H1 H2
  ipureintro; exact h

/-- A plain allocation, opened for `memset`. -/
theorem heapAfter_false {n maxP len : Nat} {live : List (Nat × Nat)} {size p : UInt32} (b : UInt8) :
    heapAfter (GF := GF) n maxP len live false size p ⊢
      ∃ bs : List UInt8, ⌜bs.length = size.toNat ∧ p.toNat + size.toNat ≤ 2 ^ 32⌝ ∗ n ↦[wms][ p.toNat ] bs ∗
        (n ↦[wms][ p.toNat ] List.replicate size.toNat b -∗ vecAfter n maxP len live size p b) := by
  iintro H
  iunfold heapAfter, content at H
  icases H with ⟨%len', %h, H1, H2⟩
  simp only [Bool.false_eq_true, ite_false]
  iunfold block at H2
  icases H2 with ⟨%bs, %hbs, H2⟩
  ihave H1 := heapInv_bound n maxP len' _ 1 $$ H1
  icases H1 with ⟨%⟨hbd, hl32⟩, H1⟩
  iexists bs
  isplitr
  · ipureintro
    refine ⟨hbs, ?_⟩
    rcases h with ⟨h0, hp, -⟩ | ⟨h0, -, -⟩
    · rw [hp, h0]; decide
    · have := hbd p.toNat size.toNat (by simp [Nat.pos_iff_ne_zero.mp h0])
      omega
  iframe H2
  iintro H2
  iunfold vecAfter
  iexists len'
  iframe H1 H2
  ipureintro; exact h

/-- The 112 bytes below `sp` as 687 uses them. -/
theorem stk112 (n a : Nat) :
    stk (GF := GF) n a 112 ⊢ stk n a 16 ∗ stk n (a + 16) 64 ∗ stk n (a + 80) 8 ∗ stk n (a + 88) 8 ∗
      stk n (a + 96) 16 := by
  iintro H
  icases stk_split n a 16 96 $$ H with ⟨H1, H⟩
  icases stk_split n (a + 16) 64 32 $$ H with ⟨H2, H⟩
  icases stk_split n (a + 16 + 64) 8 24 $$ H with ⟨H3, H⟩
  icases stk_split n (a + 16 + 64 + 8) 8 16 $$ H with ⟨H4, H5⟩
  rw [show a + 16 + 64 = a + 80 by omega, show a + 80 + 8 = a + 88 by omega,
    show a + 88 + 8 = a + 96 by omega]
  iframe H1 H2 H3 H4 H5

theorem stk112_join (n a : Nat) :
    stk (GF := GF) n a 16 ∗ stk n (a + 16) 64 ∗ stk n (a + 80) 8 ∗ stk n (a + 88) 8 ∗
      stk n (a + 96) 16 ⊢ stk n a 112 := by
  iintro ⟨H1, H2, H3, H4, H5⟩
  rw [show a + 96 = a + 88 + 8 by omega]
  ihave H4 := stk_join n (a + 88) 8 16 $$ [H4 H5]
  · iframe H4 H5
  rw [show a + 88 = a + 80 + 8 by omega]
  ihave H3 := stk_join n (a + 80) 8 24 $$ [H3 H4]
  · iframe H3 H4
  rw [show a + 80 = a + 16 + 64 by omega]
  ihave H2 := stk_join n (a + 16) 64 32 $$ [H2 H3]
  · iframe H2 H3
  iapply stk_join n a 16 96
  iframe H1 H2

/-- The cost of `from_elem(elem, c)`: the zeroed allocation, or the plain one and `memset`. -/
def cost687 (cfg : WasmConfig) (elem c : UInt32) : Nat :=
  if elem &&& 255 = 0 then 41 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAlloc cfg true c)
  else 60 * cfg.regularOpCost + (35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAlloc cfg false c)) +
    MemSet.cost c.toNat * cfg.regularOpCost

def pre687 (n g : Nat) (gt : GlobalType) (s out elem c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 elem, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗
    n ↦[wms][ out.toNat ] ob)

def post687 (n g : Nat) (gt : GlobalType) (s out elem c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗ n ↦[i32][ out.toNat + 8 ] c ∗
    vecAfter n maxP len live c p (MemSet.byteOf elem))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`vec![elem as u8; c]`** (`alloc::vec::from_elem::<u8>`, 687): the `Vec` `(ptr, c, c)` at
`out`, its `c` bytes `elem`'s low byte, the heap updated (`vecAfter`); `c < 2^28` and room for
the allocation (so neither `capacity_overflow` nor `handle_alloc_error` is reached). -/
theorem f687_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out elem c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (hs : 112 ≤ s.toNat)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c)
    (hout : out.toNat + 12 ≤ 2 ^ 32) :
    vecCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f687 Cg
        (pre687 n g gt s out elem c idx ta (A 578) maxP len live ob)
        (fun _ => cost687 cfg elem c)
        (post687 n g gt s out elem c idx ta (A 578) maxP len live) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H686 : A 686 ↪[wf] FuncInst.wasm types[31]! inst f686 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H681 : A 681 ↪[wf] FuncInst.wasm types[14]! inst f681 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H952 : A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 $$ []
  · iunfold vecCode at Hv
    icases Hv with ⟨-, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha686 := hm.funcs 686 (by decide)
  have ha681 := hm.funcs 681 (by decide)
  have ha952 := hm.funcs 952 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 32 + 8).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h32]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have hob0 : (ob.take 8).length = 8 := by simp; omega
  have hob4 : (ob.drop 8).length = 4 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre687 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho8⟩
  icases stk112 n (s.toNat - 112) $$ Hs with ⟨RA, RB, U, Z8, Z16⟩
  simp only [f687, cost687]
  by_cases he : elem &&& 255 = 0
  · ---------------------------------------------------------------- zeroed
    rw [if_pos he]
    iunfold stk at Z8
    icases Z8 with ⟨%zb, %hzb, Z⟩
    mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
    mstep; mstep
    mstep; mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep
    mcall (f686_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
        (s - 32 + 8) c true idx maxP len live zb hzb (by omega) hc28 hr) using [Hg RB Hvt Hinv Z]
    · iunfold pre686
      ihave RB := stk_addr (show s.toNat - 112 + 16 = (s - 32).toNat - 64 by omega) $$ RB
      ihave Z := memBytes_addr (show s.toNat - 112 + 88 = (s - 32 + 8).toNat by omega) $$ Z
      iframe Hg RB Hvt Hinv Z
      ipureintro; simp
    iunfold post686 at HQ
    icases HQ with ⟨%hrs, %p, Hg, RB, Hvt, Z0, Z4, HA⟩
    subst hrs
    mcredits (15 * cfg.regularOpCost + R)
    ihave Z := KeyGet.join64 n (s - 32 + 8).toNat p c $$ [Z0 Z4]
    · iframe Z0 Z4
    mstep; mstep [Z]
    rw [ofNat_decode_pair]
    mstep
    mstep; mstep; mstep [Ho8]
    mstep; mstep; mstep [Ho0]
    rw [storeBytes_pair64]
    mstep
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 32 + 32 = s by simp]
    mcredits R
    iframe Hc
    iunfold post687
    isplitr
    · ipureintro; simp [htype]
    iexists p
    ihave Ho0 := KeyGet.split64 n out.toNat p c $$ Ho0
    icases Ho0 with ⟨Ho0, Ho4⟩
    rw [byteOf_and elem he]
    iframe Hg Hvt Ho0 Ho4 Ho8
    isplitr [HA]
    · ihave RB := stk_addr (show (s - 32).toNat - 64 = s.toNat - 112 + 16 by omega) $$ RB
      ihave Z := KeyGet.split64 n _ p c $$ Z
      icases Z with ⟨Z0, Z4⟩
      ihave Z0 := stk_word n _ p $$ Z0
      ihave Z4 := stk_word n _ c $$ Z4
      ihave Z := stk_join n _ 4 4 $$ [Z0 Z4]
      · iframe Z0 Z4
      ihave Z := stk_addr (show (s - 32 + 8).toNat = s.toNat - 112 + 88 by omega) $$ Z
      iapply stk112_join
      iframe RA RB U Z Z16
    iapply heapAfter_true
    iexact HA
  · ---------------------------------------------------------------- memset
    rw [if_neg he]
    icases stk_split n (s.toNat - 112 + 96) 12 4 $$ Z16 with ⟨Z, Z12⟩
    iunfold stk at Z
    icases Z with ⟨%zb, %hzb, Z⟩
    generalize hMC : MemSet.cost c.toNat * cfg.regularOpCost = MC
    mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
    mstep; mstep
    mstep; mstep; mstep; mstep
    mstep; mstep; mstep; mstep
    mcall (f681_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
        (s - 32 + 16) c idx maxP len live zb hzb (by omega) hc28 hr) using [Hg RA RB Hvt Hinv Z]
    · iunfold pre681
      ihave RA := stk_join n (s.toNat - 112) 16 64 $$ [RA RB]
      · iframe RA RB
      ihave RA := stk_addr (show s.toNat - 112 = (s - 32).toNat - 80 by omega) $$ RA
      ihave Z := memBytes_addr (show s.toNat - 112 + 96 = (s - 32 + 16).toNat by omega) $$ Z
      iframe Hg RA Hvt Hinv Z
      ipureintro; simp
    iunfold post681 at HQ
    icases HQ with ⟨%hrs, %p, Hg, RA, Hvt, Z0, Z4, Z8', HA⟩
    subst hrs
    ihave HA := heapAfter_false (MemSet.byteOf elem) $$ HA
    icases HA with ⟨%bs, %⟨hbs, hpb⟩, Hb, HA⟩
    have h952 := MemSet.f952_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg p elem c bs
      hbs hpb
    rw [hMC] at h952
    mcredits (MC + 29 * cfg.regularOpCost + R)
    mstep; mstep [Z0]; mstep; mstep
    mcall h952 using [Hb] with (simp [activationGas, entryLocals, f952]; omega)
    · iunfold MemSet.pre
      iframe Hb
      ipureintro; rfl
    iunfold MemSet.post at HQ
    icases HQ with ⟨%hrs, Hb⟩
    subst hrs
    mcredits (14 * cfg.regularOpCost + R)
    mstep
    mstep; mstep; mstep; mstep; mstep [Ho8]
    ihave Z := KeyGet.join64 n (s - 32 + 16).toNat p c $$ [Z0 Z4]
    · iframe Z0 Z4
    mstep; mstep; mstep [Z]
    rw [ofNat_decode_pair]
    mstep [Ho0]
    rw [storeBytes_pair64]
    mstep; mstep; mstep; mstep [Hg]
    rw [show s - 32 + 32 = s by simp]
    mcredits R
    iframe Hc
    iunfold post687
    isplitr
    · ipureintro; simp [htype]
    iexists p
    ihave Ho0 := KeyGet.split64 n out.toNat p c $$ Ho0
    icases Ho0 with ⟨Ho0, Ho4⟩
    iframe Hg Hvt Ho0 Ho4 Ho8
    isplitr [HA Hb]
    · ihave RA := stk_addr (show (s - 32).toNat - 80 = s.toNat - 112 by omega) $$ RA
      ihave RA := stk_split n (s.toNat - 112) 16 64 $$ RA
      icases RA with ⟨RA, RB⟩
      ihave Z := KeyGet.split64 n _ p c $$ Z
      icases Z with ⟨Z0, Z4⟩
      ihave Z0 := stk_word n _ p $$ Z0
      ihave Z4 := stk_word n _ c $$ Z4
      ihave Z8' := stk_word n _ 0 $$ Z8'
      ihave Z := stk_join n _ 4 4 $$ [Z0 Z4]
      · iframe Z0 Z4
      ihave Z := stk_join n _ 8 4 $$ [Z Z8']
      · rw [show (s - 32 + 16).toNat + 8 = (s - 32 + 16).toNat + 8 by rfl]
        iframe Z Z8'
      ihave Z := stk_addr (show (s - 32 + 16).toNat = s.toNat - 112 + 96 by omega) $$ Z
      ihave Z := stk_join n _ 12 4 $$ [Z Z12]
      · iframe Z Z12
      iapply stk112_join
      iframe RA RB U Z8 Z
    iapply HA
    iexact Hb

end L687

end WNear.Binary.VecFromElem
