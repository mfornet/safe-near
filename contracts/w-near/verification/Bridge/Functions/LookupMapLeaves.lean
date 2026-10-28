import Bridge.Functions.StateWrite
import Bridge.Functions.ReadRegister
import Bridge.Functions.BorshInt
import Binary.Code.Part08
import Binary.Code.Part09
import Binary.Code.Part10
import Binary.Code.Part12
import Binary.Code.Part13

/-!
# The leaves of `LookupMap<String, u128>`'s `insert` (401) and `remove` (402)

```wat
;; 364 Option<Vec<u8>>::expect(out, opt, loc): [opt] = 0 → panic; out := opt (12 bytes)
;; 550 env::read_register(out, EVICTED_REGISTER): 523(out, -2)
```

* `f364_some`: `Some(vec)` copied to `out`.
* `f550_spec`: `f523_spec` at `EVICTED_REGISTER`.
-/

namespace WNear.Binary.LookupMapLeaves

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr ofNat_decode_pair storeBytes_pair64)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## `Option<Vec<u8>>::expect` (364), `Some` -/

/-- **`Option::expect`** (364) on `Some(vec)` (the pointer word `p ≠ 0`): the three words copied
to `out`. -/
theorem f364_some (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out o loc p c l : UInt32) (ob : List UInt8)
    (hob : ob.length = 12) (hp : p ≠ 0) (hout : out.toNat + 12 ≤ 2 ^ 32) (ho : o.toNat + 12 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f364 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 o, .i32 loc]⌝ ∗ n ↦[i32][ o.toNat ] p ∗
          n ↦[i32][ o.toNat + 4 ] c ∗ n ↦[i32][ o.toNat + 8 ] l ∗ n ↦[wms][ out.toNat ] ob))
        (fun _ => 15 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ o.toNat ] p ∗
          n ↦[i32][ o.toNat + 4 ] c ∗ n ↦[i32][ o.toNat + 8 ] l ∗ n ↦[i32][ out.toNat ] p ∗
          n ↦[i32][ out.toNat + 4 ] c ∗ n ↦[i32][ out.toNat + 8 ] l)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, O0, O4, O8, Ho⟩
  subst hargs
  icases U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho with ⟨Ho0, Ho8⟩
  have hob0 : (ob.take 8).length = 8 := by simp; omega
  have hob8 : (ob.drop 8).length = 4 := by simp; omega
  simp only [f364]
  mstep; mstep; mstep [O0]
  mstep_taken with (simp [hp])
  ihave O := KeyGet.join64 n o.toNat p c $$ [O0 O4]
  · iframe O0 O4
  mstep; mstep; mstep [O]
  rw [ofNat_decode_pair]
  mstep [Ho0]
  rw [storeBytes_pair64]
  ihave O8 := memBytes_addr (show o.toNat + 8 = (o + 8).toNat by simp [UInt32.toNat_add]; omega) $$ O8
  ihave Ho8 := memBytes_addr (show out.toNat + 8 = (out + 8).toNat by simp [UInt32.toNat_add]; omega) $$ Ho8
  mstep; mstep; mstep; mstep; mstep; mstep; mstep [O8]; mstep [Ho8]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  ihave O := KeyGet.split64 n o.toNat p c $$ O
  icases O with ⟨O0, O4⟩
  ihave Ho0 := KeyGet.split64 n out.toNat p c $$ Ho0
  icases Ho0 with ⟨Ho0, Ho4⟩
  ihave O8 := memBytes_addr (show (o + 8).toNat = o.toNat + 8 by simp [UInt32.toNat_add]; omega) $$ O8
  ihave Ho8 := memBytes_addr (show (out + 8).toNat = out.toNat + 8 by simp [UInt32.toNat_add]; omega) $$ Ho8
  iframe O0 O4 O8 Ho0 Ho4 Ho8

/-! ## `env::read_register(EVICTED_REGISTER)` (550) -/

open WNear.Binary.ReadRegister (rrCode pre523 post523 cost523 RegOk f523_spec)
open WNear.Binary.StorageWrite (evictedRegister)
open WNear.Binary.AllocFirstFit (vt)

/-- The code of 550 (persistent). -/
def rr550Code (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) : IProp GF :=
  iprop(rrCode e inst mi A n maxP mx ∗ A 523 ↪[wf] FuncInst.wasm types[5]! inst f523)

instance (e inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n maxP : Nat) (mx : Option Nat) :
    Persistent (rr550Code (GF := GF) e inst mi A n maxP mx) := by
  unfold rr550Code; infer_instance

def pre550 (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (s out : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (ob : List UInt8) (h : NearState) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out]⌝ ∗ pre523 n g ta A gt s out evictedRegister idx maxP len live ob h
    [.i32 out, .i64 evictedRegister])

set_option maxRecDepth 100000 in
/-- **`env::read_register(EVICTED_REGISTER)`** (550): `f523_spec` at `u64::MAX - 1`. -/
theorem f550_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (s out : UInt32) (hs : 160 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hout : out.toNat + 12 ≤ 2 ^ 32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (h : NearState)
    (hok : RegOk maxP len (h.registers evictedRegister.toNat)) :
    rr550Code e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f550 Cg
        (pre550 n g ta A gt s out idx maxP len live ob h)
        (fun _ => 13 * cfg.regularOpCost + cost523 cfg h evictedRegister)
        (post523 n g ta A gt s out evictedRegister idx maxP len live h) := by
  iintro #Hk
  iunfold rr550Code at Hk
  icases Hk with ⟨#Hrr, #F523⟩
  ihave #S523 := f523_spec (GF := GF) cfg lim (d + 1) types[5]! (by rfl) inst mi e A n g ta mx hm (by omega) Cg gt s
    out hs hal hout evictedRegister idx maxP len live ob hob h hok $$ Hrr
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold rrCode, ReadRegister.ifaceCodeR, Interface.ifaceCode at Hrr
    icases Hrr with ⟨⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩, -⟩
    iexact Hi
  have ha523 := hm.funcs 523 (by decide)
  have t5 : types[5]!.params.length = 2 := by rfl
  generalize hK : cost523 cfg h evictedRegister = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre550 at HP
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f550]
  mstep; mstep
  mcall S523 using [HP] with (rw [hK]; mstep_norm_full; omega)
  · rw [show (18446744073709551614 : UInt64) = evictedRegister from rfl]; iexact HP
  iunfold post523 at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc
  iunfold post523
  iframe HQ
  ipureintro; simp [htype]


/-! ## `Vec::with_capacity_in` (505, the body of 373) -/

open WNear.Binary.VecFromElem (roomFor heapAfter)
open WNear.Binary.VecWithCap (okG costAllocF vecCode2 pre767 post767 f767_spec pre373 post373)
open WNear.Binary.AllocZeroed (allocCode)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`Vec::<u8>::with_capacity_in(out, c)`** (505, the body of 373): the `Vec` `(ptr, c, 0)` at
`out`, the allocation as `heapAfter` (for `c ≠ 0`: a live block of `c` bytes). -/
theorem f505_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (hs : 80 ≤ s.toNat)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c)
    (F : Nat := 1) (hF : okG F := by decide) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f505 Cg
        (pre373 n g gt s out c idx ta (A 578) maxP len live F ob)
        (fun _ => 35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAllocF cfg F c))
        (post373 n g gt s out c idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H767 : A 767 ↪[wf] FuncInst.wasm types[31]! inst f767 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha767 := hm.funcs 767 (by decide)
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
  iunfold pre373 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 8 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho8⟩
  icases stk_split n (s.toNat - 80) 64 16 $$ Hs with ⟨X, Hs⟩
  icases stk_split n (s.toNat - 80 + 64) 8 8 $$ Hs with ⟨Y, Z⟩
  iunfold stk at Z
  icases Z with ⟨%zb, %hzb, Z⟩
  simp only [f505]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  have hG : VecWithCap.costAllocG cfg false F c = costAllocF cfg F c := by simp [VecWithCap.costAllocG]
  mcall (f767_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16 + 8) c false idx maxP len live zb hzb (by omega) hc28 hr (F := F) (hF := hF) (hFz := fun h => by cases h)) using [Hg X Hvt Hinv Z]
  · iunfold pre767
    ihave X := stk_addr (show s.toNat - 80 = (s - 16).toNat - 64 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 80 + 64 + 8 = (s - 16 + 8).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; simp
  iunfold post767 at HQ
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
  iunfold post373
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

/-! ## The total length of two slices (426, 495) -/

/-- The two slices `(p1, l1)`, `(p2, l2)` at `a` (four words). -/
def slices2 (n : Nat) (a p1 l1 p2 l2 : UInt32) : IProp GF :=
  iprop(n ↦[i32][ a.toNat ] p1 ∗ n ↦[i32][ a.toNat + 4 ] l1 ∗ n ↦[i32][ a.toNat + 8 ] p2 ∗
    n ↦[i32][ a.toNat + 12 ] l2)

/-- The loop invariant of 426 on two slices: before the first, the second, or none left. -/
def inv426 (n inst : Nat) (mi : ModuleInst) (Cg R c₀ : Nat) (a p1 l1 p2 l2 : UInt32) :
    List Value → Frame → IProp GF := fun X g =>
  iprop(⌜X = []⌝ ∗ slices2 n a p1 l1 p2 l2 ∗ ∃ t : UInt32,
    ((⌜g = ⟨#[.i32 a, .i32 16, .i32 0, .i32 t], inst, mi⟩⌝ ∗ credits Cg (51 * c₀ + R)) ∨
     (⌜g = ⟨#[.i32 (a + 8), .i32 8, .i32 l1, .i32 t], inst, mi⟩⌝ ∗ credits Cg (28 * c₀ + R)) ∨
     (⌜g = ⟨#[.i32 (a + 16), .i32 0, .i32 (l1 + l2), .i32 t], inst, mi⟩⌝ ∗ credits Cg (5 * c₀ + R))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The sum of the slices' lengths** (426) over two slices at `a`, from 0: `l1 + l2` (no
overflow). -/
theorem f426_two (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (a p1 l1 p2 l2 : UInt32)
    (ha : a.toNat + 16 < 2 ^ 32) (hl : l1.toNat + l2.toNat < 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f426 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 (a + 16), .i32 0]⌝ ∗ slices2 n a p1 l1 p2 l2))
        (fun _ => 56 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 (l1 + l2)]⌝ ∗ slices2 n a p1 l1 p2 l2)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HS⟩
  subst hargs
  have h8 : (a + 8).toNat = a.toNat + 8 := by simp [UInt32.toNat_add]; omega
  have h16 : (a + 16).toNat = a.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have hs16 : a + 16 - a = 16 := by rw [UInt32.add_comm]; simp
  simp only [f426]
  mstep; mstep; mstep; mstep
  rw [hs16]
  mstep; mstep
  iapply mwpi_loop0 (Cg := Cg) (R := 51 * cfg.regularOpCost + R)
    (I := inv426 n inst mi Cg R cfg.regularOpCost a p1 l1 p2 l2) _ _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv426 at HI
    icases HI with ⟨%hX, HS, %t, HI⟩
    subst hX
    iunfold slices2 at HS
    icases HS with ⟨S0, S4, S8, S12⟩
    icases HI with (⟨%hg, Hc⟩ | ⟨%hg, Hc⟩ | ⟨%hg, Hc⟩)
    · rw [hg]
      mstep; mstep; mstep
      mstep; mstep; mstep [S4]; mstep; mstep; mstep; mstep; mstep
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep
      simp only [Post.mloop]
      iapply pure_pay_intro'
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; exact ⟨by simp, by omega⟩
      inext
      iintro Hc
      iunfold inv426
      isplitr
      · ipureintro; rfl
      iunfold slices2
      iframe S0 S4 S8 S12
      iexists 0 + l1
      iright; ileft
      isplitr
      · ipureintro; simp
      iapply credits_le
      iframe Hc
      ipureintro; omega
    · rw [hg]
      ihave S12 := memBytes_addr (show a.toNat + 12 = (a + 8).toNat + 4 by omega) $$ S12
      mstep; mstep; mstep
      mstep; mstep; mstep [S12]; mstep; mstep; mstep; mstep
      have hlt : ¬ (l1 + l2 < l1) := by
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_add, Nat.mod_eq_of_lt hl]; omega
      mstep_not_taken with (simp [Numeric.bool, Numeric.irelop32, hlt])
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      simp only [Post.mloop]
      iapply pure_pay_intro'
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; exact ⟨by simp, by omega⟩
      inext
      iintro Hc
      iunfold inv426
      isplitr
      · ipureintro; rfl
      ihave S12 := memBytes_addr (show (a + 8).toNat + 4 = a.toNat + 12 by omega) $$ S12
      iunfold slices2
      iframe S0 S4 S8 S12
      iexists l1 + l2
      iright; iright
      isplitr
      · ipureintro; simp [UInt32.add_assoc]
      iapply credits_le
      iframe Hc
      ipureintro; omega
    · rw [hg]
      mstep; mstep; mstep
      simp only [Post.mloop]
      mstep_post
      mstep; mstep
      mcredits R
      iframe Hc
      isplitr
      · ipureintro; simp [htype]
      iunfold slices2
      iframe S0 S4 S8 S12
  isplitl [Hc]
  · rw [show cfg.regularOpCost + (51 * cfg.regularOpCost + R) = 52 * cfg.regularOpCost + R by omega]
    iexact Hc
  inext
  iintro Hc
  iunfold inv426
  isplitr
  · ipureintro; rfl
  iframe HS
  iexists 0
  ileft
  iframe Hc
  ipureintro; rfl

/-- **The sum of the slices' lengths** (495 = 426 from 0) over two slices at `a`. -/
theorem f495_two (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (a p1 l1 p2 l2 : UInt32)
    (ha : a.toNat + 16 < 2 ^ 32) (hl : l1.toNat + l2.toNat < 2 ^ 32) :
    A 426 ↪[wf] FuncInst.wasm types[15]! inst f426 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f495 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 (a + 16)]⌝ ∗ slices2 n a p1 l1 p2 l2))
        (fun _ => 70 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 (l1 + l2)]⌝ ∗ slices2 n a p1 l1 p2 l2)) := by
  iintro ⟨#H426, #Hi⟩
  have hn := hm.mem
  have ha426 := hm.funcs 426 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HS⟩
  subst hargs
  simp only [f495]
  mstep; mstep; mstep
  mcall (f426_two cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg a p1 l1 p2 l2 ha hl) using [HS]
  · iframe HS
  icases HQ with ⟨%hrs, HS⟩
  subst hrs
  repeat mstep
  mpay
  iframe Hc HS
  ipureintro; simp [htype]

end Spec

end WNear.Binary.LookupMapLeaves
