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

/-! ## `[&[u8]]::concat` of two slices (510) -/

open WNear.Binary.VecAppend (appCode f711_room)
open WNear.Binary.FmtSink (roomPre roomPost grown heapAfter_grown)
open WNear.Binary.AllocInv (heapInv)

/-- The code of 510 (persistent). -/
def code510 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(vecCode2 n maxP inst mi A ∗ appCode inst mi A ∗ A 426 ↪[wf] FuncInst.wasm types[15]! inst f426 ∗
    A 495 ↪[wf] FuncInst.wasm types[13]! inst f495 ∗ A 505 ↪[wf] FuncInst.wasm types[14]! inst f505)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code510 (GF := GF) n maxP inst mi A) := by
  unfold code510; infer_instance

def pre510 (n g : Nat) (gt : GlobalType) (s out a p1 l1 p2 l2 : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (b1 b2 ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 a, .i32 2]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗
    vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗ slices2 n a p1 l1 p2 l2 ∗
    n ↦[wms][ p1.toNat ] b1 ∗ n ↦[wms][ p2.toNat ] b2 ∗ n ↦[wms][ out.toNat ] ob)

/-- The `Vec` `(q, l1 + l2, l1 + l2)` at `out` holding `b1 ++ b2`, a fresh live block. -/
def post510 (n g : Nat) (gt : GlobalType) (s out a p1 l1 p2 l2 : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (b1 b2 : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗
    slices2 n a p1 l1 p2 l2 ∗ n ↦[wms][ p1.toNat ] b1 ∗ n ↦[wms][ p2.toNat ] b2 ∗
    ∃ q : UInt32, ⌜q ≠ 0 ∧ q.toNat + (l1 + l2).toNat < 2 ^ 32⌝ ∗ grown n maxP len live F q (l1 + l2) ∗
      n ↦[i32][ out.toNat ] q ∗ n ↦[i32][ out.toNat + 4 ] (l1 + l2) ∗ n ↦[i32][ out.toNat + 8 ] (l1 + l2) ∗
      n ↦[wms][ q.toNat ] (b1 ++ b2))

/-- The loop invariant of 510: before the first slice, the second, or none left. -/
def inv510 (n g inst : Nat) (mi : ModuleInst) (Cg R c₀ M1 M2 : Nat) (gt : GlobalType) (s out a p1 l1 p2 l2 q : UInt32)
    (b1 b2 bs : List UInt8) (Fr : IProp GF) : List Value → Frame → IProp GF := fun X f =>
  iprop(⌜X = []⌝ ∗ Fr ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ slices2 n a p1 l1 p2 l2 ∗
    n ↦[wms][ p1.toNat ] b1 ∗ n ↦[wms][ p2.toNat ] b2 ∗ n ↦[i32][ out.toNat ] q ∗
    n ↦[i32][ out.toNat + 4 ] (l1 + l2) ∗
    ((⌜f = ⟨#[.i32 out, .i32 a, .i32 16], inst, mi⟩⌝ ∗ n ↦[i32][ out.toNat + 8 ] 0 ∗
        n ↦[wms][ q.toNat ] (bs.take l1.toNat) ∗
        n ↦[wms][ q.toNat + l1.toNat ] (bs.drop l1.toNat) ∗ credits Cg (400 * c₀ + M1 + M2 + R)) ∨
     (⌜f = ⟨#[.i32 out, .i32 (a + 8), .i32 8], inst, mi⟩⌝ ∗ n ↦[i32][ out.toNat + 8 ] (0 + l1) ∗
        n ↦[wms][ q.toNat ] b1 ∗ n ↦[wms][ q.toNat + l1.toNat ] (bs.drop l1.toNat) ∗ credits Cg (250 * c₀ + M2 + R)) ∨
     (⌜f = ⟨#[.i32 out, .i32 (a + 16), .i32 0], inst, mi⟩⌝ ∗ n ↦[i32][ out.toNat + 8 ] (0 + l1 + l2) ∗
        n ↦[wms][ q.toNat ] b1 ∗ n ↦[wms][ q.toNat + l1.toNat ] b2 ∗ credits Cg (100 * c₀ + R))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`[&[u8]]::concat`** (510) of the two slices at `a`: a fresh `Vec` with capacity `l1 + l2`
(505), each slice appended (711). -/
theorem f510_two (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out a p1 l1 p2 l2 : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (b1 b2 ob : List UInt8)
    (hs : 80 ≤ s.toNat) (hob : ob.length = 12) (hb1 : b1.length = l1.toNat) (hb2 : b2.length = l2.toNat)
    (hl : l1.toNat + l2.toNat < 2 ^ 28) (hl0 : 0 < l1.toNat + l2.toNat)
    (ha : a.toNat + 16 < 2 ^ 32) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hp1 : p1.toNat + l1.toNat ≤ 2 ^ 32) (hp2 : p2.toNat + l2.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP (l1 + l2)) :
    code510 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f510 Cg
        (pre510 n g gt s out a p1 l1 p2 l2 idx ta (A 578) maxP len live F b1 b2 ob)
        (fun _ => 1000 * cfg.regularOpCost + costAllocF cfg F (l1 + l2) +
          MemCpy.cost l1.toNat * cfg.regularOpCost + MemCpy.cost l2.toNat * cfg.regularOpCost)
        (post510 n g gt s out a p1 l1 p2 l2 idx ta (A 578) maxP len live F b1 b2) := by
  iintro #Hk
  iunfold code510 at Hk
  icases Hk with ⟨#Hv, #Ha, #H426, #H495, #H505⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold appCode at Ha; icases Ha with ⟨-, -, -, -, -, -, #H⟩; iexact H
  ihave #H711 : A 711 ↪[wf] FuncInst.wasm types[31]! inst f711 $$ []
  · iunfold appCode at Ha; icases Ha with ⟨-, -, -, -, #H, -, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha495 := hm.funcs 495 (by decide)
  have ha505 := hm.funcs 505 (by decide)
  have ha711 := hm.funcs 711 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h8 : (a + 8).toNat = a.toNat + 8 := by simp [UInt32.toNat_add]; omega
  have h16 : (a + 16).toNat = a.toNat + 16 := by simp [UInt32.toNat_add]; omega
  have hT : (l1 + l2).toNat = l1.toNat + l2.toNat := by rw [UInt32.toNat_add]; omega
  generalize hM1 : MemCpy.cost l1.toNat * cfg.regularOpCost = M1
  generalize hM2 : MemCpy.cost l2.toNat * cfg.regularOpCost = M2
  generalize hKA : costAllocF cfg F (l1 + l2) = KA
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre510 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, HS, B1, B2, Ho⟩
  subst hargs
  simp only [f510]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [show (2 : UInt32) <<< (3 % 32) = 16 from rfl]
  mcall (f495_two cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg a p1 l1 p2 l2 ha (by omega))
    using [HS]
  · iframe HS
  icases HQ with ⟨%hrs, HS⟩
  subst hrs
  mcall (f505_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s out (l1 + l2) idx
      maxP len live ob hob hs (by omega) (fun _ => hr) F hF) using [Hg Hs Hvt Hinv Ho]
  · iunfold pre373
    iframe Hg Hs Hvt Hinv Ho
    ipureintro; rfl
  iunfold post373 at HQ
  icases HQ with ⟨%hrs, %q, Hg, Hs, Hvt, O0, O4, O8, HA⟩
  subst hrs
  rw [hKA]
  icases heapAfter_grown (by omega) $$ HA with ⟨%⟨hq0, hqb⟩, Hblk, Hgr⟩
  iunfold AllocInv.block at Hblk
  icases Hblk with ⟨%bs, %hbs, Hblk⟩
  ihave Hblk := U128From.memBytes_split n q.toNat l1.toNat bs (by omega) $$ Hblk
  icases Hblk with ⟨Q1, Q2⟩
  icases stk_split n (s.toNat - 80) 64 16 $$ Hs with ⟨Lo, Hs⟩
  rw [show s.toNat - 80 + 64 = s.toNat - 16 by omega]
  have hc0 : (0 : UInt32).toNat = 0 := rfl
  have hX1 : (11 + (115 + MemCpy.cost l1.toNat)) * cfg.regularOpCost = 126 * cfg.regularOpCost + M1 := by
    rw [← hM1, Nat.add_mul, Nat.add_mul]; omega
  have hX2 : (11 + (115 + MemCpy.cost l2.toNat)) * cfg.regularOpCost = 126 * cfg.regularOpCost + M2 := by
    rw [← hM2, Nat.add_mul, Nat.add_mul]; omega
  have hl1 : (0 + l1).toNat = l1.toNat := by simp
  have hl12 : (0 + l1 + l2).toNat = l1.toNat + l2.toNat := by simp [hT]
  have hbt : (bs.take l1.toNat).length = l1.toNat := by simp; omega
  have hbd : (bs.drop l1.toNat).length = l2.toNat := by simp; omega
  iapply mwpi_loop0 (Cg := Cg) (R := 400 * cfg.regularOpCost + M1 + M2 + R)
    (I := inv510 n g inst mi Cg R cfg.regularOpCost M1 M2 gt s out a p1 l1 p2 l2 q b1 b2 bs
      iprop(stk n (s.toNat - 80) 64 ∗ vt n 1057464 idx ta (A 578) ∗ grown n maxP len live F q (l1 + l2))) _ _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv510 at HI
    icases HI with ⟨%hX, Fr, Hg, Hs, HS, B1, B2, O0, O4, HI⟩
    subst hX
    iunfold slices2 at HS
    icases HS with ⟨S0, S4, S8, S12⟩
    icases HI with (⟨%hf, O8, Q1, Q2, Hc⟩ | ⟨%hf, O8, Q1, Q2, Hc⟩ | ⟨%hf, O8, Q1, Q2, Hc⟩)
    · rw [hf]
      mstep; mstep; mstep
      mstep; mstep; mstep [S0]; mstep; mstep [S4]
      mcall (f711_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
          gt s out q (l1 + l2) 0 p1 l1 (bs.take l1.toNat) b1 (by omega) hbt hb1 (by omega)
          (by rw [hc0, hT]; omega) (by omega) hp1) using [Hg Hs O0 O4 O8 Q1 B1]
          with (mstep_norm_full; rw [hX1]; omega)
      · iunfold roomPre
        simp only [hc0, Nat.add_zero]
        iframe Hg Hs O0 O4 O8 Q1 B1
      icases HQ with ⟨%hrs, HQ⟩
      subst hrs
      rw [show (7 + (11 + (115 + MemCpy.cost l1.toNat))) * cfg.regularOpCost = 133 * cfg.regularOpCost + M1 by
        rw [← hM1]; simp only [Nat.add_mul]; omega]
      iunfold roomPost at HQ
      icases HQ with ⟨Hg, Hs, O0, O4, O8, Q1, B1⟩
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      simp only [Post.mloop]
      iapply pure_pay_intro'
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; exact ⟨by simp, by omega⟩
      inext
      iintro Hc
      iunfold inv510
      isplitr
      · ipureintro; rfl
      iunfold slices2
      iframe Fr Hg Hs S0 S4 S8 S12 B1 B2 O0 O4
      iright; ileft
      iframe O8 Q1 Q2
      isplitr
      · ipureintro; simp
      iapply credits_le
      iframe Hc
      ipureintro; omega
    · rw [hf]
      ihave S8 := memBytes_addr (show a.toNat + 8 = (a + 8).toNat by omega) $$ S8
      ihave S12 := memBytes_addr (show a.toNat + 12 = (a + 8).toNat + 4 by omega) $$ S12
      mstep; mstep; mstep
      mstep; mstep; mstep [S8]; mstep; mstep [S12]
      ihave Q2 := memBytes_addr (show q.toNat + l1.toNat = q.toNat + (0 + l1).toNat by rw [hl1]) $$ Q2
      mcall (f711_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
          gt s out q (l1 + l2) (0 + l1) p2 l2 (bs.drop l1.toNat) b2 (by omega) hbd hb2 (by omega)
          (by rw [hl1, hT] <;> omega) (by omega) hp2) using [Hg Hs O0 O4 O8 Q2 B2]
          with (mstep_norm_full; rw [hX2]; omega)
      · iunfold roomPre
        iframe Hg Hs O0 O4 O8 Q2 B2
      icases HQ with ⟨%hrs, HQ⟩
      subst hrs
      rw [show (7 + (11 + (115 + MemCpy.cost l2.toNat))) * cfg.regularOpCost = 133 * cfg.regularOpCost + M2 by
        rw [← hM2]; simp only [Nat.add_mul]; omega]
      iunfold roomPost at HQ
      icases HQ with ⟨Hg, Hs, O0, O4, O8, Q2, B2⟩
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      simp only [Post.mloop]
      iapply pure_pay_intro'
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; exact ⟨by simp, by omega⟩
      inext
      iintro Hc
      iunfold inv510
      isplitr
      · ipureintro; rfl
      ihave S8 := memBytes_addr (show (a + 8).toNat = a.toNat + 8 by omega) $$ S8
      ihave S12 := memBytes_addr (show (a + 8).toNat + 4 = a.toNat + 12 by omega) $$ S12
      ihave Q2 := memBytes_addr (show q.toNat + (0 + l1).toNat = q.toNat + l1.toNat by rw [hl1]) $$ Q2
      iunfold slices2
      iframe Fr Hg Hs S0 S4 S8 S12 B1 B2 O0 O4
      iright; iright
      iframe O8 Q1 Q2
      isplitr
      · ipureintro; simp [UInt32.add_assoc]
      iapply credits_le
      iframe Hc
      ipureintro; omega
    · rw [hf]
      mstep; mstep; mstep; mstep
      rw [show (0 : UInt32) + l1 + l2 = l1 + l2 by simp]
      simp only [Post.mloop]
      mpay
      mcredits R
      iframe Hc
      iunfold post510
      isplitr
      · ipureintro; simp [htype]
      icases Fr with ⟨Lo, Hvt, Hgr⟩
      iunfold slices2
      iframe Hg Hvt S0 S4 S8 S12 B1 B2
      isplitl [Lo Hs]
      · ihave X := stk_join n (s.toNat - 80) 64 16 $$ [Lo Hs]
        · rw [show s.toNat - 80 + 64 = s.toNat - 16 by omega]; iframe Lo Hs
        iexact X
      iexists q
      iframe Hgr O0 O4 O8
      isplitr
      · ipureintro; exact ⟨hq0, hqb⟩
      iapply BorshFT.joinB (n := n) (a := q.toNat) (b := q.toNat + l1.toNat) b1 b2 (by omega)
      iframe Q1 Q2
  isplitl [Hc]
  · iapply credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro Hc
  iunfold inv510
  isplitr
  · ipureintro; rfl
  iframe Lo Hvt Hgr Hg Hs HS B1 B2 O0 O4
  ileft
  iframe O8 Q1 Q2 Hc
  ipureintro; rfl

/-! ## `[a, b].concat()` (519) -/

/-- The code of 519 (persistent). -/
def code519 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code510 n maxP inst mi A ∗ A 510 ↪[wf] FuncInst.wasm types[31]! inst f510)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code519 (GF := GF) n maxP inst mi A) := by
  unfold code519; infer_instance

def pre519 (n g : Nat) (gt : GlobalType) (s out p1 l1 p2 l2 : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (b1 b2 ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 p1, .i32 l1, .i32 p2, .i32 l2]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ p1.toNat ] b1 ∗ n ↦[wms][ p2.toNat ] b2 ∗ n ↦[wms][ out.toNat ] ob)

/-- The `Vec` `(q, l1 + l2, l1 + l2)` at `out` holding `b1 ++ b2`, a fresh live block. -/
def post519 (n g : Nat) (gt : GlobalType) (s out p1 l1 p2 l2 : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (b1 b2 : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 96) 96 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[wms][ p1.toNat ] b1 ∗ n ↦[wms][ p2.toNat ] b2 ∗
    ∃ q : UInt32, ⌜q ≠ 0 ∧ q.toNat + (l1 + l2).toNat < 2 ^ 32⌝ ∗ grown n maxP len live F q (l1 + l2) ∗
      n ↦[i32][ out.toNat ] q ∗ n ↦[i32][ out.toNat + 4 ] (l1 + l2) ∗ n ↦[i32][ out.toNat + 8 ] (l1 + l2) ∗
      n ↦[wms][ q.toNat ] (b1 ++ b2))

/-- The cost of 510 on slices of `l1` and `l2` bytes. -/
def cost510 (cfg : WasmConfig) (F : Nat) (l1 l2 : UInt32) : Nat :=
  1000 * cfg.regularOpCost + costAllocF cfg F (l1 + l2) +
    MemCpy.cost l1.toNat * cfg.regularOpCost + MemCpy.cost l2.toNat * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`[a, b].concat()`** (519): the two slices on a 16-byte frame, 510. -/
theorem f519_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out p1 l1 p2 l2 : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (b1 b2 ob : List UInt8)
    (hs : 96 ≤ s.toNat) (hob : ob.length = 12) (hb1 : b1.length = l1.toNat) (hb2 : b2.length = l2.toNat)
    (hl : l1.toNat + l2.toNat < 2 ^ 28) (hl0 : 0 < l1.toNat + l2.toNat) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hp1 : p1.toNat + l1.toNat ≤ 2 ^ 32) (hp2 : p2.toNat + l2.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP (l1 + l2)) :
    code519 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f519 Cg
        (pre519 n g gt s out p1 l1 p2 l2 idx ta (A 578) maxP len live F b1 b2 ob)
        (fun _ => 40 * cfg.regularOpCost + cost510 cfg F l1 l2)
        (post519 n g gt s out p1 l1 p2 l2 idx ta (A 578) maxP len live F b1 b2) := by
  iintro #Hk
  iunfold code519 at Hk
  icases Hk with ⟨#H510c, #H510⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code510, appCode at H510c; icases H510c with ⟨-, ⟨-, -, -, -, -, -, #H⟩, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha510 := hm.funcs 510 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  generalize hK : cost510 cfg F l1 l2 = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre519 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, B1, B2, Ho⟩
  subst hargs
  icases stk_split n (s.toNat - 96) 80 16 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 96 + 80 = s.toNat - 16 by omega]
  icases VecFromElem.stk_split n (s.toNat - 16) 4 12 $$ Fr with ⟨F0, Fr⟩
  icases VecFromElem.stk_split n (s.toNat - 16 + 4) 4 8 $$ Fr with ⟨F4, Fr⟩
  icases VecFromElem.stk_split n (s.toNat - 16 + 4 + 4) 4 4 $$ Fr with ⟨F8, F12⟩
  icases ReadRegister.stk4_word n _ $$ F0 with ⟨%w0, F0⟩
  icases ReadRegister.stk4_word n _ $$ F4 with ⟨%w4, F4⟩
  icases ReadRegister.stk4_word n _ $$ F8 with ⟨%w8, F8⟩
  icases ReadRegister.stk4_word n _ $$ F12 with ⟨%w12, F12⟩
  ihave F0 := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ F0
  ihave F4 := memBytes_addr (show s.toNat - 16 + 4 = (s - 16).toNat + 4 by omega) $$ F4
  ihave F8 := memBytes_addr (show s.toNat - 16 + 4 + 4 = (s - 16).toNat + 8 by omega) $$ F8
  ihave F12 := memBytes_addr (show s.toNat - 16 + 4 + 4 + 4 = (s - 16).toNat + 12 by omega) $$ F12
  simp only [f519]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep [F12]
  mstep; mstep; mstep [F8]
  mstep; mstep; mstep [F4]
  mstep; mstep; mstep [F0]
  mstep; mstep; mstep
  mcall (f510_two cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16) out (s - 16)
      p1 l1 p2 l2 idx maxP len live F hF b1 b2 ob (by omega) hob hb1 hb2 hl hl0 (by omega) hout hp1 hp2 hr)
      using [Hg Lo Hvt Hinv F0 F4 F8 F12 B1 B2 Ho] with (rw [← hK]; unfold cost510; mstep_norm_full; omega)
  · iunfold pre510, slices2
    ihave Lo := stk_addr (show s.toNat - 96 = (s - 16).toNat - 80 by omega) $$ Lo
    iframe Hg Lo Hvt Hinv F0 F4 F8 F12 B1 B2 Ho
    ipureintro; rfl
  iunfold post510 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, HS, B1, B2, HQ⟩
  subst hrs
  rw [show 1000 * cfg.regularOpCost + costAllocF cfg F (l1 + l2) + MemCpy.cost l1.toNat * cfg.regularOpCost +
    MemCpy.cost l2.toNat * cfg.regularOpCost = K by rw [← hK]; rfl]
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post519
  isplitr
  · ipureintro; simp [htype]
  iframe Hg Hvt B1 B2 HQ
  iunfold slices2 at HS
  icases HS with ⟨F0, F4, F8, F12⟩
  ihave F0 := stk_word n _ _ $$ F0
  ihave F4 := stk_word n _ _ $$ F4
  ihave F8 := stk_word n _ _ $$ F8
  ihave F12 := stk_word n _ _ $$ F12
  ihave X := StateWrite.stkJ (n := n) (show (s - 16).toNat + 4 = (s - 16).toNat + 4 by rfl) $$ [F0 F4]
  · iframe F0 F4
  ihave X := StateWrite.stkJ (n := n) (show (s - 16).toNat + 8 = (s - 16).toNat + (4 + 4) by rfl) $$ [X F8]
  · iframe X F8
  ihave X := StateWrite.stkJ (n := n) (show (s - 16).toNat + 12 = (s - 16).toNat + (4 + 4 + 4) by rfl) $$ [X F12]
  · iframe X F12
  ihave Y := StateWrite.stkJ (n := n) (show (s - 16).toNat = (s - 16).toNat - 80 + 80 by omega) $$ [Lo X]
  · iframe Lo X
  iapply StateWrite.stkL (n := n) (show (s - 16).toNat - 80 = s.toNat - 96 by omega) (by rfl)
  iexact Y

/-! ## The storage key `prefix ++ key` (392) -/

/-- The code of 392 (persistent). -/
def code392 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code519 n maxP inst mi A ∗ A 519 ↪[wf] FuncInst.wasm types[39]! inst f519 ∗
    A 779 ↪[wf] FuncInst.wasm types[14]! inst f779)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code392 (GF := GF) n maxP inst mi A) := by
  unfold code392; infer_instance

/-- The map's prefix `Vec` `(pp, pc, pl)` at `m`. -/
def prefixAt (n : Nat) (m pp pc pl : UInt32) : IProp GF :=
  iprop(n ↦[wms][ m.toNat ] (bytes32 pp ++ (bytes32 pc ++ bytes32 pl)))

def pre392 (n g : Nat) (gt : GlobalType) (s out m pp pc pl kp kl : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (pre key ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 m, .i32 kp, .i32 kl]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗ n ↦[wms][ kp.toNat ] key ∗ n ↦[wms][ out.toNat ] ob)

/-- The storage key `pre ++ key` in a fresh `Vec` `(q, pl + kl, pl + kl)` at `out`. -/
def post392 (n g : Nat) (gt : GlobalType) (s out m pp pc pl kp kl : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (pre key : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    prefixAt n m pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗ n ↦[wms][ kp.toNat ] key ∗
    ∃ q : UInt32, ⌜q ≠ 0 ∧ q.toNat + (pl + kl).toNat < 2 ^ 32⌝ ∗ grown n maxP len live F q (pl + kl) ∗
      n ↦[i32][ out.toNat ] q ∗ n ↦[i32][ out.toNat + 4 ] (pl + kl) ∗ n ↦[i32][ out.toNat + 8 ] (pl + kl) ∗
      n ↦[wms][ q.toNat ] (pre ++ key))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The storage key of a `LookupMap` entry** (392): the map's prefix (779) and the key's bytes
concatenated (519). -/
theorem f392_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out m pp pc pl kp kl : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (pre key ob : List UInt8)
    (hs : 112 ≤ s.toNat) (hob : ob.length = 12) (hpre : pre.length = pl.toNat) (hkey : key.length = kl.toNat)
    (hl : pl.toNat + kl.toNat < 2 ^ 28) (hl0 : 0 < pl.toNat + kl.toNat) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hkp : kp.toNat + kl.toNat ≤ 2 ^ 32)
    (hr : roomFor len maxP (pl + kl)) :
    code392 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f392 Cg
        (pre392 n g gt s out m pp pc pl kp kl idx ta (A 578) maxP len live F pre key ob)
        (fun _ => 100 * cfg.regularOpCost + cost510 cfg F pl kl)
        (post392 n g gt s out m pp pc pl kp kl idx ta (A 578) maxP len live F pre key) := by
  iintro #Hk
  iunfold code392 at Hk
  icases Hk with ⟨#H519c, #H519, #H779⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code519, code510, appCode at H519c; icases H519c with ⟨⟨-, ⟨-, -, -, -, -, -, #H⟩, -⟩, -⟩; iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha519 := hm.funcs 519 (by decide)
  have ha779 := hm.funcs 779 (by decide)
  have t39 : types[39]!.params.length = 5 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 8 := by simp [UInt32.toNat_add, h16]; omega
  generalize hK : cost510 cfg F pl kl = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre392 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hm, Hp, Hkey, Ho⟩
  subst hargs
  iunfold prefixAt at Hm
  icases stk_split n (s.toNat - 112) 96 16 $$ Hs with ⟨Lo, Fr⟩
  rw [show s.toNat - 112 + 96 = s.toNat - 16 by omega]
  icases stk_split n (s.toNat - 16) 8 8 $$ Fr with ⟨F0, F8⟩
  iunfold stk at F8
  icases F8 with ⟨%fb, %hfb, F8⟩
  ihave F8 := memBytes_addr (show s.toNat - 16 + 8 = (s - 16 + 8).toNat by omega) $$ F8
  simp only [f392]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (VecDeref.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s - 16 + 8) m fb
      (bytes32 pp ++ (bytes32 pc ++ bytes32 pl)) hfb (by simp [bytes32])) using [F8 Hm]
  · iunfold VecDeref.pre
    iframe F8 Hm
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, F8, Hm⟩
  subst hrs
  have hpl : (bytes32 pp ++ (bytes32 pc ++ bytes32 pl)).take 4 ++ (bytes32 pp ++ (bytes32 pc ++ bytes32 pl)).drop 8 =
      bytes32 pp ++ bytes32 pl := by
    have l4 : ∀ x : UInt32, (bytes32 x).length = 4 := fun x => by simp [bytes32]
    rw [List.take_left' (l4 pp), ← List.append_assoc, List.drop_left' (by simp [l4])]
  rw [hpl]
  ihave F8 := KeyGet.split64 n (s - 16 + 8).toNat pp pl $$ F8
  icases F8 with ⟨P0, P4⟩
  mstep; mstep; mstep [P0]; mstep; mstep [P4]; mstep; mstep
  mcall (f519_spec cfg lim (d + 1) types[39]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16) out pp pl kp kl
      idx maxP len live F hF pre key ob (by omega) hob hpre hkey hl hl0 hout hpp hkp hr)
      using [Hg Lo Hvt Hinv Hp Hkey Ho] with (rw [hK]; mstep_norm_full; omega)
  · iunfold pre519
    ihave Lo := stk_addr (show s.toNat - 112 = (s - 16).toNat - 96 by omega) $$ Lo
    iframe Hg Lo Hvt Hinv Hp Hkey Ho
    ipureintro; rfl
  rw [hK]
  iunfold post519 at HQ
  icases HQ with ⟨%hrs, Hg, Lo, Hvt, Hp, Hkey, HQ⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  mcredits R
  iframe Hc
  iunfold post392, prefixAt
  isplitr
  · ipureintro; simp [htype]
  iframe Hg Hvt Hm Hp Hkey HQ
  ihave P0 := stk_word n _ _ $$ P0
  ihave P4 := stk_word n _ _ $$ P4
  ihave X := StateWrite.stkJ (n := n) (show (s - 16 + 8).toNat + 4 = (s - 16 + 8).toNat + 4 by rfl) $$ [P0 P4]
  · iframe P0 P4
  ihave X := StateWrite.stkJ (n := n) (show (s - 16 + 8).toNat = s.toNat - 16 + 8 by omega) $$ [F0 X]
  · iframe F0 X
  ihave Y := StateWrite.stkJ (n := n) (show s.toNat - 16 = (s - 16).toNat - 96 + 96 by omega) $$ [Lo X]
  · iframe Lo X
  iapply StateWrite.stkL (n := n) (show (s - 16).toNat - 96 = s.toNat - 112 by omega) (by rfl)
  iexact Y

end Spec

end WNear.Binary.LookupMapLeaves
