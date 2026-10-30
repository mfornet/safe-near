import Bridge.Functions.AllocZeroedF

/-!
# `vec![0u8; c]` (687 → 686 → 690 → 689 → `__rust_alloc_zeroed`) on `heapInv … F`, any `F ≥ 1`

`VecFromElem.lean`'s zeroed path on any free-list bound `F ≥ 1` (`okG F`), its proofs with
`AllocZeroedF.f313_specF` in place of `AllocZeroed.f313_spec_room`; only the zeroed path
(`init = true`, `elem & 255 = 0`) is lifted, the one `read_register` takes.

* `f689_specZ`: `alloc_impl(size, 1, true)`, 27 `regular_op_cost`s and `costZeroF cfg F size`;
* `f690_specF`: `Global::allocate_zeroed`, 35 more;
* `f686_specZ`: `RawVec::allocate_in(cap, true)`, `203 · regular_op_cost + costZeroF cfg F c`;
* `f687_specZ`: `vec![elem; c]` for `elem & 255 = 0`, `cost687Z cfg F c =
  41 · regular_op_cost + (203 · regular_op_cost + costZeroF cfg F c)` (`cost687Z_one`: at `F = 1`,
  `VecFromElem.cost687 cfg elem c`).

The code is `vecCodeF`: `vecCode` and the merge 575.
-/

namespace WNear.Binary.VecFromElemF

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocNewCell (cellPages memBytes_addr)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (pair64 storeBytes_pair64 ofNat_decode_pair stk stk_split stk_join stk_word stk_addr
  roomFor grownLen content heapAfter vecCode memBytes_nil stk_open581 stk_close581 pre68x post68x les_neg1
  heapAfter_ne stk64 stk64_join stk112 stk112_join byteOf_and cost687)
open WNear.Binary.AllocZeroed (allocCode)
open WNear.Binary.AllocZeroedF (code575F costZeroF zeroedPostF f313_specF costZeroF_one)
open WNear.Binary.VecWithCap (okG)

section Code

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `vecCode` and the merge 575 (persistent). -/
def vecCodeF (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(vecCode n maxP inst mi A ∗ A 575 ↪[wf] FuncInst.wasm types[0]! inst f575)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (vecCodeF (GF := GF) n maxP inst mi A) := by
  unfold vecCodeF; infer_instance

end Code

/-! ## `alloc_impl(size, 1, true)` (689) -/

section L689

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre689Z (n g : Nat) (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 size, .i32 1, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ out.toNat ] ob)

def post689Z (n g : Nat) (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size ∗ heapAfter n maxP len live F true size p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `alloc_impl(size, 1, true)` (689) on `heapInv … F`: no allocation for `size = 0` (the pointer 1),
else `__rust_alloc_zeroed`; `(ptr, size)` at `out`. -/
theorem f689_specZ (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8) (hob : ob.length = 8) (hs : 16 ≤ s.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size) :
    vecCodeF n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f689 Cg
        (pre689Z n g gt s out size idx ta (A 578) maxP len live F ob)
        (fun _ => 27 * cfg.regularOpCost + costZeroF cfg F size)
        (post689Z n g gt s out size idx ta (A 578) maxP len live F) := by
  iintro #Hv
  iunfold vecCodeF at Hv
  icases Hv with ⟨#Hv, #H575⟩
  iunfold vecCode at Hv
  icases Hv with ⟨#Hcode, #H581, #H952, #H153, #H239, #H313, #H236, #H310, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold allocCode at Hcode
    icases Hcode with ⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  ihave #HC5 : code575F (GF := GF) n maxP inst mi A $$ []
  · iunfold code575F
    isplitr
    · iexact Hcode
    · iexact H575
  have hn := hm.mem
  have ha313 := hm.funcs 313 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre689Z at HP
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
    iunfold post689Z
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
    simp only [ite_true, List.replicate_zero]
    iapply memBytes_nil
  · ---------------------------------------------------------------- __rust_alloc_zeroed
    have hpos : 0 < size.toNat := Nat.pos_of_ne_zero h0
    have hne : size ≠ 0 := fun e => h0 (by simp [e])
    have hroom := hr hpos
    icases stk_open581 n s hs $$ Hs with ⟨%o1, %o2, %o4, %⟨h1, h2, h4⟩, O1, O2, O4, W8⟩
    have h313 := f313_specF (GF := GF) cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s
      size 1 idx 0 maxP len live F o1 o2 o4 hs rfl (by decide) hpos hsize2 hroom.1 hroom.2.1 h1 h2 h4
      hroom.2.2.1 hroom.2.2.2 hF
    simp only [costZeroF]
    generalize 14 * cfg.regularOpCost + AllocZeroedF.cost153F cfg F size 1 = K at h313 ⊢
    mstep; mstep; mstep; mstep
    mstep; mstep; mstep; mstep
    mstep; mstep
    mcall h313 using [Hg O1 O2 O4 Hvt Hinv]
      with (simp [activationGas, entryLocals, f313]; omega)
    · iframe Hg O1 O2 O4 Hvt Hinv
    iunfold zeroedPostF at HQ
    icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %len', %hl', Hinv, Hb⟩
    subst hrs
    mcredits (8 * cfg.regularOpCost + R)
    mstep; mstep
    mstep
    mstep; mstep [Ho4]
    mstep; mstep; mstep [Ho0]
    mcredits R
    iframe Hc
    iunfold post689Z
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

/-! ## `Global::allocate_zeroed` (690) -/

section L690

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `Global::allocate_zeroed` (690) on `heapInv … F`: `alloc_impl(size, 1, true)` (689) into its
frame, `(ptr, size)` copied to `out`. -/
theorem f690_specF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8) (hob : ob.length = 8) (hs : 32 ≤ s.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size) :
    vecCodeF n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f690 Cg
        (pre68x n g gt s out size idx ta (A 578) maxP len live F ob)
        (fun _ => 35 * cfg.regularOpCost + (27 * cfg.regularOpCost + costZeroF cfg F size))
        (post68x n g gt s out size true idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCodeF, vecCode, allocCode at Hv
    icases Hv with ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩, -⟩
    iexact Hi
  ihave #H689 : A 689 ↪[wf] FuncInst.wasm types[45]! inst f689 $$ []
  · iunfold vecCodeF, vecCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, #H, -⟩, -⟩
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
  mcall (f689_specZ cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16 + 8) size idx maxP len live F hF zb hzb (by omega) hsize2 hr) using [Hg X Hvt Hinv Z]
  · iunfold pre689Z
    ihave X := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 32 + 16 + 8 = (s - 16 + 8).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; simp
  iunfold post689Z at HQ
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

end L690

/-! ## `RawVec::allocate_in(cap, true)` (686) -/

section L686

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.VecFromElem (pre685 post685 f685_spec)

def pre686Z (n g : Nat) (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ out.toNat ] ob)

def post686Z (n g : Nat) (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗ heapAfter n maxP len live F true c p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `RawVec::<u8>::allocate_in(cap, true)` (686) on `heapInv … F`: `(ptr, cap)` at `out`, zeroed;
`cap < 2^28`, with room. -/
theorem f686_specZ (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8) (hob : ob.length = 8) (hs : 64 ≤ s.toNat)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c) :
    vecCodeF n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f686 Cg
        (pre686Z n g gt s out c idx ta (A 578) maxP len live F ob)
        (fun _ => 203 * cfg.regularOpCost + costZeroF cfg F c)
        (post686Z n g gt s out c idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCodeF, vecCode, allocCode at Hv
    icases Hv with ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩, -⟩
    iexact Hi
  ihave #H685 : A 685 ↪[wf] FuncInst.wasm types[14]! inst f685 $$ []
  · iunfold vecCodeF, vecCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, #H, -⟩, -⟩
    iexact H
  ihave #H684 : A 684 ↪[wf] FuncInst.wasm types[14]! inst f684 $$ []
  · iunfold vecCodeF, vecCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, #H, -⟩, -⟩
    iexact H
  ihave #H690 : A 690 ↪[wf] FuncInst.wasm types[31]! inst f690 $$ []
  · iunfold vecCodeF, vecCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha685 := hm.funcs 685 (by decide)
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
  iunfold pre686Z at HP
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
  iunfold stk at Z8
  icases Z8 with ⟨%zb, %hzb, Z⟩
  mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mcall (f690_specF cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 8) c idx maxP len live F hF zb hzb (by omega) hc28 hr) using [Hg R1 R2 Hvt Hinv Z]
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
  iunfold post686Z
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

/-! ## `vec![0u8; c]` (687) -/

section L687

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `VecFromElem.vecAfter` on `heapInv … F`. -/
def vecAfterF (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (size p : UInt32) (b : UInt8) : IProp GF :=
  iprop(∃ len', ⌜(size.toNat = 0 ∧ p = 1 ∧ len' = len) ∨
      (0 < size.toNat ∧ p ≠ 0 ∧ (len' = len ∨ len' = grownLen len size))⌝ ∗
    heapInv n maxP len' (if size.toNat = 0 then live else (p.toNat, size.toNat) :: live) F ∗
    n ↦[wms][ p.toNat ] List.replicate size.toNat b)

theorem heapAfter_trueF {n maxP len : Nat} {live : List (Nat × Nat)} {F : Nat} {size p : UInt32} :
    heapAfter (GF := GF) n maxP len live F true size p ⊢ vecAfterF n maxP len live F size p 0 := by
  iintro H
  iunfold heapAfter, content at H
  icases H with ⟨%len', %h, H1, H2⟩
  iunfold vecAfterF
  iexists len'
  simp only [ite_true]
  iframe H1 H2
  ipureintro; exact h

/-- The cost of `vec![0u8; c]` on `heapInv … F`. -/
def cost687Z (cfg : WasmConfig) (F : Nat) (c : UInt32) : Nat :=
  41 * cfg.regularOpCost + (203 * cfg.regularOpCost + costZeroF cfg F c)

theorem cost687Z_one (cfg : WasmConfig) (elem c : UInt32) (he : elem &&& 255 = 0) :
    cost687Z cfg 1 c = cost687 cfg elem c := by
  simp [cost687Z, cost687, he, costZeroF_one]

def pre687F (n g : Nat) (gt : GlobalType) (s out elem c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 elem, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ out.toNat ] ob)

def post687F (n g : Nat) (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗ n ↦[i32][ out.toNat + 8 ] c ∗
    vecAfterF n maxP len live F c p 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`vec![elem as u8; c]`** (687) for `elem & 255 = 0`, on `heapInv … F`: the `Vec` `(ptr, c, c)`
at `out`, its `c` bytes zero, the heap updated (`vecAfterF`); `c < 2^28`, with room. -/
theorem f687_specZ (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out elem c : UInt32) (he : elem &&& 255 = 0) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob : List UInt8) (hob : ob.length = 12)
    (hs : 112 ≤ s.toNat) (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c)
    (hout : out.toNat + 12 ≤ 2 ^ 32) :
    vecCodeF n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f687 Cg
        (pre687F n g gt s out elem c idx ta (A 578) maxP len live F ob)
        (fun _ => cost687Z cfg F c)
        (post687F n g gt s out c idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCodeF, vecCode, allocCode at Hv
    icases Hv with ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩, -⟩
    iexact Hi
  ihave #H686 : A 686 ↪[wf] FuncInst.wasm types[31]! inst f686 $$ []
  · iunfold vecCodeF, vecCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha686 := hm.funcs 686 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 32 + 8).toNat = s.toNat - 24 := by simp [UInt32.toNat_add, h32]; omega
  have hob0 : (ob.take 8).length = 8 := by simp; omega
  have hob4 : (ob.drop 8).length = 4 := by simp; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre687F at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho8⟩
  icases stk112 n (s.toNat - 112) $$ Hs with ⟨RA, RB, U, Z8, Z16⟩
  simp only [f687, cost687Z]
  iunfold stk at Z8
  icases Z8 with ⟨%zb, %hzb, Z⟩
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mcall (f686_specZ cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 8) c idx maxP len live F hF zb hzb (by omega) hc28 hr) using [Hg RB Hvt Hinv Z]
  · iunfold pre686Z
    ihave RB := stk_addr (show s.toNat - 112 + 16 = (s - 32).toNat - 64 by omega) $$ RB
    ihave Z := memBytes_addr (show s.toNat - 112 + 88 = (s - 32 + 8).toNat by omega) $$ Z
    iframe Hg RB Hvt Hinv Z
    ipureintro; simp
  iunfold post686Z at HQ
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
  iunfold post687F
  isplitr
  · ipureintro; simp [htype]
  iexists p
  ihave Ho0 := KeyGet.split64 n out.toNat p c $$ Ho0
  icases Ho0 with ⟨Ho0, Ho4⟩
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
  iapply heapAfter_trueF
  iexact HA

end L687

end WNear.Binary.VecFromElemF
