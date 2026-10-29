import Bridge.Functions.VecFromElem
import Bridge.Functions.AllocTwoHeap
import Bridge.Functions.AllocWalkHeap

/-!
# `Vec::<u8>::with_capacity` (373) and the `RawVec` allocation below it (Borsh's copy)

Borsh's `Vec<u8>` deserialization allocates through a second monomorphization of the `RawVec`
chain of VecFromElem.lean. The bodies are those of VecFromElem.lean up to the indices of the
calls (and the panic locations, on paths not taken):

| here | VecFromElem | |
|---|---|---|
| 751 | 684 | `Layout::array::<u8>` |
| 752 | 685 | `Layout::array` |
| 770 | 689 | `alloc_impl` |
| 769 / 774 | 688 / 690 | `Global::allocate` / `allocate_zeroed` |
| 767 | 686 | `RawVec::allocate_in` |
| 373 | 681 | `Vec::with_capacity_in` |

The proofs are VecFromElem.lean's, renamed; the code they run is `vecCode2`.

*The free-list bound `F`.* The non-zeroed path (770 → 769 → 767 → 373) is stated on
`heapInv … F` for any `F ≥ 1` (`okG`, an optional argument defaulting to `F = 1`), at the
allocator's cost `costAllocF cfg F size` (`f310_roomG`): for `F ≤ 2` it is `costAlloc cfg false size`
(`costAllocF_le2`; `F = 1` through `AllocSeq.f310_spec_room`, `F = 2`, the heap `state_read`
leaves, through `AllocTwo.f310_spec_two`: `f310_roomF`), above it the general walk's
`AllocWalk.cost310W cfg F size 1` (`AllocWalk.f310_spec_walk`, `970 + 320 · F` `regular_op_cost`s
and the grow). The allocation keeps the bound. The zeroed path (`__rust_alloc_zeroed`, 774) stays
on `F = 1`; 770 and 767 charge `costAllocG cfg z F size` (`costAlloc` for `z`).
-/

namespace WNear.Binary.VecWithCap

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocNewCell (cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (pair64 storeBytes_pair64 load_pair64 ofNat_decode_pair layout_size stk stk_split
  stk_join stk_intro stk_word stk16 stk16_join roomFor grownLen content heapAfter costAlloc f310_room memBytes_nil
  stk_open581 stk_close581 stk_addr pre68x post68x les_neg1 heapAfter_ne stk64 stk64_join)

section Code

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocZeroed (allocCode)

/-- The code `Vec::with_capacity` (373) runs (persistent); the slots as in `vecCode2`. -/
def vecCode2 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(allocCode n maxP inst mi A ∗
    A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗ A 952 ↪[wf] FuncInst.wasm types[15]! inst f952 ∗
    A 153 ↪[wf] FuncInst.wasm types[15]! inst f153 ∗ A 239 ↪[wf] FuncInst.wasm types[13]! inst f239 ∗
    A 313 ↪[wf] FuncInst.wasm types[13]! inst f313 ∗ A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗
    A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗ A 751 ↪[wf] FuncInst.wasm types[14]! inst f751 ∗
    A 752 ↪[wf] FuncInst.wasm types[14]! inst f752 ∗ A 770 ↪[wf] FuncInst.wasm types[45]! inst f770 ∗
    A 769 ↪[wf] FuncInst.wasm types[31]! inst f769 ∗ A 774 ↪[wf] FuncInst.wasm types[31]! inst f774 ∗
    A 767 ↪[wf] FuncInst.wasm types[31]! inst f767 ∗ A 373 ↪[wf] FuncInst.wasm types[14]! inst f373 ∗
    A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗ A 575 ↪[wf] FuncInst.wasm types[0]! inst f575)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (vecCode2 (GF := GF) n maxP inst mi A) := by
  unfold vecCode2; infer_instance

end Code

/-! ## `Layout::array::<u8>` (751) -/

section L751

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre751 (n g : Nat) (gt : GlobalType) (s out lp c : UInt32) (ob0 ob4 : List UInt8) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i32 lp]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ n ↦[i32][ lp.toNat ] c ∗
    n ↦[i32][ lp.toNat + 4 ] 1 ∗ n ↦[wms][ out.toNat ] ob0 ∗ n ↦[wms][ out.toNat + 4 ] ob4)

def post751 (n g : Nat) (gt : GlobalType) (s out lp c : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ n ↦[i32][ lp.toNat ] c ∗
    n ↦[i32][ lp.toNat + 4 ] 1 ∗ n ↦[i32][ out.toNat ] c ∗ n ↦[i32][ out.toNat + 4 ] 1)

/-- `Layout::array::<u8>` (751) on `(c, 1)`: the layout `(c, 1)` at `out`. -/
theorem f751_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (Cg : Nat)
    (gt : GlobalType) (s out lp c : UInt32) (ob0 ob4 : List UInt8)
    (hob0 : ob0.length = 4) (hob4 : ob4.length = 4) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f751 Cg (pre751 n g gt s out lp c ob0 ob4)
        (fun _ => 33 * cfg.regularOpCost) (post751 n g gt s out lp c) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre751 at HP
  icases HP with ⟨%hargs, Hg, Hc0, Hc4, Ho0, Ho4⟩
  subst hargs
  simp only [f751]
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
  iunfold post751
  iframe Hg Hc0 Hc4 Ho0 Ho4
  ipureintro; simp [htype]

end L751

/-! ## `Layout::array` (752) -/

section L752

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)


def pre752 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (ob : List UInt8) (args : List Value) :
    IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
    n ↦[wms][ out.toNat ] ob)

def post752 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
    n ↦[i32][ out.toNat ] c ∗ n ↦[i32][ out.toNat + 4 ] 1)

/-- `Layout::array::<u8>(cap)` (752): `(cap, 1)` at `out`. -/
theorem f752_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (ob : List UInt8) (hob : ob.length = 8)
    (hs : 16 ≤ s.toNat) :
    A 751 ↪[wf] FuncInst.wasm types[14]! inst f751 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f752 Cg (pre752 n g gt s out c ob)
        (fun _ => 67 * cfg.regularOpCost) (post752 n g gt s out c) := by
  iintro ⟨#H751, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha751 := hm.funcs 751 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e8 : (s - 16 + 8).toNat = s.toNat - 16 + 8 := by simp [UInt32.toNat_add, h16]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre752 at HP
  icases HP with ⟨%hargs, Hg, Hs, Ho⟩
  subst hargs
  icases stk16 n (s.toNat - 16) $$ Hs with ⟨W0, W4, W8, W12⟩
  iunfold stk at W0 W4 W8 W12
  icases W0 with ⟨%b0, %hb0, W0⟩
  icases W4 with ⟨%b4, %hb4, W4⟩
  icases W8 with ⟨%b8, %hb8, W8⟩
  icases W12 with ⟨%b12, %hb12, W12⟩
  simp only [f752]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep [W12]
  mstep; mstep; mstep [W8]
  mstep; mstep; mstep; mstep
  mcall (f751_spec cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg Cg gt (s - 16) (s - 16)
      (s - 16 + 8) c b0 b4 hb0 hb4) using [Hg W0 W4 W8 W12]
  · iunfold pre751
    ihave W8 := memBytes_addr (show s.toNat - 16 + 8 = (s - 16 + 8).toNat by omega) $$ W8
    ihave W12 := memBytes_addr (show s.toNat - 16 + 12 = (s - 16 + 8).toNat + 4 by omega) $$ W12
    ihave W0 := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ W0
    ihave W4 := memBytes_addr (show s.toNat - 16 + 4 = (s - 16).toNat + 4 by omega) $$ W4
    iframe Hg W0 W4 W8 W12
    ipureintro; rfl
  iunfold post751 at HQ
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
  iunfold post752
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

end L752

/-! ## The allocation (770) -/

section L770

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode cost153 cost581 zeroedPost f313_spec_room)

/-- The free-list bounds the allocation chain is stated on: 1 (any sequence of allocations
without frees) or 2 (after `state_read`'s free). -/
def okF (F : Nat) : Prop := F = 1 ∨ F = 2

/-- `VecFromElem.f310_room` on `heapInv … F`, `okF F`: `AllocSeq.f310_spec_room` for `F = 1`,
`AllocTwo.f310_spec_two` (which needs 575, the merge) for `F = 2`. The bound is kept. -/
theorem f310_roomF (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8) (hsp : 16 ≤ sp.toNat)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4) (hr : roomFor len maxP size)
    (hF : okF F) :
    allocCode n maxP inst mi A ∗ A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗
      A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗ A 575 ↪[wf] FuncInst.wasm types[0]! inst f575
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => 15 * cfg.regularOpCost + (15 * cfg.regularOpCost + (910 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) 1).toNat)))
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % (1 : UInt32).toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) 1).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) F ∗ block n p.toNat size.toNat)) := by
  rcases hF with rfl | rfl
  · iintro ⟨#Hc, #H236, #H581, -⟩
    iapply (f310_room cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size idx maxP len live
      o1 o2 o4 hsp hsize hsize2 ho1 ho2 ho4 hr)
    iframe Hc H236 H581
  · obtain ⟨hlen0, hlen1, hroom, hmax⟩ := hr
    iintro ⟨#Hc, #H236, #H581, #H575⟩
    iunfold allocCode at Hc
    icases Hc with ⟨#H0, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11⟩
    iapply (AllocTwo.f310_spec_two cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size 1 idx maxP len
      live 2 o1 o2 o4 hsp rfl (by omega) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax)
    iunfold AllocTwo.code310
    iframe H0 H236 H581 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H575 H11

/-- The free-list bounds the general walk allocates on: any `F ≥ 1`. -/
abbrev okG (F : Nat) : Prop := 1 ≤ F

theorem okG_of_okF {F : Nat} (h : okF F) : okG F := by
  unfold okG; rcases h with rfl | rfl <;> decide

/-- `__rust_alloc(size, 1)`'s cost on `heapInv … F`: `costAlloc` for `F ≤ 2`, the general walk's
`AllocWalk.cost310W` above. -/
def costAllocF (cfg : WasmConfig) (F : Nat) (size : UInt32) : Nat :=
  if F ≤ 2 then costAlloc cfg false size else AllocWalk.cost310W cfg F size 1

theorem costAllocF_le2 (cfg : WasmConfig) {F : Nat} (h : F ≤ 2) (size : UInt32) :
    costAllocF cfg F size = costAlloc cfg false size := by
  simp [costAllocF, h]

/-- The allocator's cost in `alloc_impl` (770): `__rust_alloc_zeroed` (`z`, on `F = 1`) or
`__rust_alloc` on `heapInv … F`. -/
def costAllocG (cfg : WasmConfig) (z : Bool) (F : Nat) (size : UInt32) : Nat :=
  if z then costAlloc cfg true size else costAllocF cfg F size

theorem costAllocG_le2 (cfg : WasmConfig) (z : Bool) {F : Nat} (h : F ≤ 2) (size : UInt32) :
    costAllocG cfg z F size = costAlloc cfg z size := by
  cases z <;> simp [costAllocG, costAllocF_le2 cfg h, costAlloc]

/-- `f310_roomF` for any `F ≥ 1`: a block, the bound `F` kept, at `costAllocF cfg F size`. -/
theorem f310_roomG (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat)
    (o1 o2 o4 : List UInt8) (hsp : 16 ≤ sp.toNat)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4) (hr : roomFor len maxP size)
    (hF : okG F) :
    allocCode n maxP inst mi A ∗ A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗
      A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗ A 575 ↪[wf] FuncInst.wasm types[0]! inst f575
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 1]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F))
        (fun _ => costAllocF cfg F size)
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p] ∧ p ≠ 0 ∧ p.toNat % (1 : UInt32).toNat = 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          ∃ len', ⌜len' = len ∨ len' = len + (cellPages (wordsOf size) 1).toNat * 65536⌝ ∗
            heapInv n maxP len' ((p.toNat, size.toNat) :: live) F ∗ block n p.toNat size.toNat)) := by
  unfold okG at hF
  by_cases h2 : F ≤ 2
  · rw [show (fun _ : List Value => costAllocF cfg F size) = (fun _ => 15 * cfg.regularOpCost +
        (15 * cfg.regularOpCost + (910 * cfg.regularOpCost + cfg.linearOpBaseCost +
          cfg.linearOpUnitCost * (cellPages (wordsOf size) 1).toNat))) from by
      funext _; rw [costAllocF_le2 cfg h2]; rfl]
    exact f310_roomF cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size idx maxP len live F o1 o2 o4 hsp
      hsize hsize2 ho1 ho2 ho4 hr (by unfold okF; omega)
  · obtain ⟨hlen0, hlen1, hroom, hmax⟩ := hr
    rw [show (fun _ : List Value => costAllocF cfg F size) = (fun _ => AllocWalk.cost310W cfg F size 1) from by
      funext _; simp [costAllocF, h2]]
    have hmx : max F 1 = F := Nat.max_eq_left hF
    iintro ⟨#Hc, #H236, #H581, #H575⟩
    iunfold allocCode at Hc
    icases Hc with ⟨#H0, #H1, #H2, #H3, #H4, #H5, #H6, #H7, #H8, #H9, #H10, #H11⟩
    have key := AllocWalk.f310_spec_walk (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size 1 idx 0
      maxP len live F o1 o2 o4 hsp rfl (by decide) hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 hroom hmax
    rw [hmx] at key
    iapply key
    iunfold AllocTwo.code310
    iframe H0 H236 H581 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H575 H11


/-- Room for an allocation of `size` bytes (align 1) on a heap of length `len`, under the
limit `maxP`. -/
def pre770 (n g : Nat) (gt : GlobalType) (s out size : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 size, .i32 1, .i32 (if z then 1 else 0)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ out.toNat ] ob)

def post770 (n g : Nat) (gt : GlobalType) (s out size : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] size ∗ heapAfter n maxP len live F z size p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `alloc_impl(size, 1, z)` (770): no allocation for `size = 0` (the pointer 1), else
`__rust_alloc_zeroed` (`z`) or `__rust_alloc`; `(ptr, size)` at `out`. -/
theorem f770_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size : UInt32) (z : Bool) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 8) (hs : 16 ≤ s.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size)
    (F : Nat := 1) (hF : okG F := by decide) (hFz : z = true → F = 1 := by exact fun _ => rfl) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f770 Cg
        (pre770 n g gt s out size z idx ta (A 578) maxP len live F ob)
        (fun _ => 27 * cfg.regularOpCost + costAllocG cfg z F size)
        (post770 n g gt s out size z idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #H575 : A 575 ↪[wf] FuncInst.wasm types[0]! inst f575 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H⟩
    iexact H
  iunfold vecCode2 at Hv
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
  iunfold pre770 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : (ob.drop 4).length = 4 := by simp; omega
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  simp only [f770]
  by_cases h0 : size.toNat = 0
  · ---------------------------------------------------------------- size 0
    have hz : size = 0 := UInt32.toNat_inj.mp (by simpa using h0)
    subst hz
    mstep; mstep; mstep; mstep
    mstep; mstep; mstep [Ho4]
    mstep; mstep; mstep [Ho0]
    mcredits R
    iframe Hc
    iunfold post770
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
      simp only [Bool.false_eq_true, ite_false, costAllocG]
      mstep; mstep; mstep; mstep
      mstep; mstep; mstep; mstep
      mstep; mstep
      mcall (f310_roomG cfg lim (d + 1) types[13]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s size idx maxP
          len live F o1 o2 o4 hs hpos hsize2 h1 h2 h4 hroom hF) using [Hg O1 O2 O4 Hvt Hinv]
      · iframe Hg O1 O2 O4 Hvt Hinv
      icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %len', %hl', Hinv, Hb⟩
      subst hrs
      mcredits (7 * cfg.regularOpCost + R)
      mstep; mstep; mstep; mstep [Ho4]
      mstep; mstep; mstep [Ho0]
      mcredits R
      iframe Hc
      iunfold post770
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
      obtain rfl : F = 1 := hFz rfl
      simp only [ite_true, costAllocG, costAlloc]
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
      iunfold post770
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

end L770

/-! ## `Global::allocate` (769) and `allocate_zeroed` (774) -/

section L68x

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `Global::allocate_zeroed` (774): `alloc_impl(size, 1, true)` (770) into its frame, `(ptr, size)`
copied to `out`. -/
theorem f774_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 8) (hs : 32 ≤ s.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f774 Cg
        (pre68x n g gt s out size idx ta (A 578) maxP len live 1 ob)
        (fun _ => 35 * cfg.regularOpCost + (27 * cfg.regularOpCost + costAlloc cfg true size))
        (post68x n g gt s out size true idx ta (A 578) maxP len live 1) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H770 : A 770 ↪[wf] FuncInst.wasm types[45]! inst f770 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha770 := hm.funcs 770 (by decide)
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
  simp only [f774]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  have hG : costAllocG cfg true 1 size = costAlloc cfg true size := by simp [costAllocG]
  mcall (f770_spec cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16 + 8) size true idx maxP len live zb hzb (by omega) hsize2 hr) using [Hg X Hvt Hinv Z]
  · iunfold pre770
    ihave X := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 32 + 16 + 8 = (s - 16 + 8).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; simp
  iunfold post770 at HQ
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
/-- `Global::allocate` (769): `alloc_impl(size, 1, false)` (770) into its frame, `(ptr, size)`
copied to `out`. -/
theorem f769_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out size : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 8) (hs : 32 ≤ s.toNat)
    (hsize2 : size.toNat < 2 ^ 28) (hr : 0 < size.toNat → roomFor len maxP size)
    (F : Nat := 1) (hF : okG F := by decide) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f769 Cg
        (pre68x n g gt s out size idx ta (A 578) maxP len live F ob)
        (fun _ => 35 * cfg.regularOpCost + (27 * cfg.regularOpCost + costAllocF cfg F size))
        (post68x n g gt s out size false idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H770 : A 770 ↪[wf] FuncInst.wasm types[45]! inst f770 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha770 := hm.funcs 770 (by decide)
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
  simp only [f769]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  have hG : costAllocG cfg false F size = costAllocF cfg F size := by simp [costAllocG]
  mcall (f770_spec cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 16)
      (s - 16 + 8) size false idx maxP len live zb hzb (by omega) hsize2 hr (F := F) (hF := hF)
      (hFz := fun h => by cases h)) using [Hg X Hvt Hinv Z]
  · iunfold pre770
    ihave X := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ X
    ihave Z := memBytes_addr (show s.toNat - 32 + 16 + 8 = (s - 16 + 8).toNat by omega) $$ Z
    iframe Hg X Hvt Hinv Z
    ipureintro; simp
  iunfold post770 at HQ
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

/-! ## `RawVec::allocate_in` (767) -/

section L767

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)


def pre767 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c, .i32 (if z then 1 else 0)]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ out.toNat ] ob)

def post767 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (z : Bool) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗ heapAfter n maxP len live F z c p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `RawVec::<u8>::allocate_in(cap, init)` (767): `(ptr, cap)` at `out`, zeroed for `init`;
`cap < 2^28` (so no `capacity_overflow`), with room (so no `handle_alloc_error`). -/
theorem f767_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (z : Bool) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 8) (hs : 64 ≤ s.toNat)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c)
    (F : Nat := 1) (hF : okG F := by decide) (hFz : z = true → F = 1 := by exact fun _ => rfl) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f767 Cg
        (pre767 n g gt s out c z idx ta (A 578) maxP len live F ob)
        (fun _ => 203 * cfg.regularOpCost + costAllocG cfg z F c)
        (post767 n g gt s out c z idx ta (A 578) maxP len live F) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H752 : A 752 ↪[wf] FuncInst.wasm types[14]! inst f752 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H751 : A 751 ↪[wf] FuncInst.wasm types[14]! inst f751 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H774 : A 774 ↪[wf] FuncInst.wasm types[31]! inst f774 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H769 : A 769 ↪[wf] FuncInst.wasm types[31]! inst f769 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have hg := hm.glob
  have ha752 := hm.funcs 752 (by decide)
  have ha769 := hm.funcs 769 (by decide)
  have ha774 := hm.funcs 774 (by decide)
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
  iunfold pre767 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  icases stk64 n (s.toNat - 64) $$ Hs with ⟨R1, R2, U, Z8, Z16, L⟩
  iunfold stk at L
  icases L with ⟨%lb, %hlb, L⟩
  simp only [f767]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  mcall (f752_spec cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
      (s - 32 + 24) c lb hlb (by omega)) using [Hg R2 L]
  · iunfold pre752
    ihave R2 := stk_addr (show s.toNat - 64 + 16 = (s - 32).toNat - 16 by omega) $$ R2
    ihave L := memBytes_addr (show s.toNat - 64 + 56 = (s - 32 + 24).toNat by omega) $$ L
    iframe Hg R2 L
    ipureintro; rfl
  iunfold post752 at HQ
  icases HQ with ⟨%hrs, Hg, R2, L0, L4⟩
  subst hrs
  ihave R2 := stk_addr (show (s - 32).toNat - 16 = s.toNat - 64 + 16 by omega) $$ R2
  mstep; mstep; mstep; mstep [L4]; mstep; mstep; mstep
  mstep; mstep [L0]; mstep; mstep; mstep; mstep
  mstep; mstep
  cases z
  · -------------------------------------------------------------- init = false
    simp only [Bool.false_eq_true, ite_false, costAllocG]
    iunfold stk at Z16
    icases Z16 with ⟨%zb, %hzb, Z⟩
    mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep
    mcall (f769_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
        (s - 32 + 16) c idx maxP len live zb hzb (by omega) hc28 hr (F := F) (hF := hF)) using [Hg R1 R2 Hvt Hinv Z]
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
    iunfold post767
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
    obtain rfl : F = 1 := hFz rfl
    simp only [ite_true, costAllocG]
    iunfold stk at Z8
    icases Z8 with ⟨%zb, %hzb, Z⟩
    mstep; mstep; mstep
    mstep; mstep; mstep; mstep; mstep
    mcall (f774_spec cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt (s - 32)
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
    iunfold post767
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

end L767

/-! ## `Vec::with_capacity_in` (373) -/

section L373

variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)

def pre373 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ out.toNat ] ob)

def post373 (n g : Nat) (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] c ∗ n ↦[i32][ out.toNat + 8 ] 0 ∗
    heapAfter n maxP len live F false c p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- `Vec::<u8>::with_capacity_in(cap)` (373): the `Vec` `(ptr, cap, 0)` at `out`. -/
theorem f373_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 10 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 12) (hs : 80 ≤ s.toNat)
    (hc28 : c.toNat < 2 ^ 28) (hr : 0 < c.toNat → roomFor len maxP c)
    (F : Nat := 1) (hF : okG F := by decide) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f373 Cg
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
  simp only [f373]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep
  have hG : costAllocG cfg false F c = costAllocF cfg F c := by simp [costAllocG]
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

end L373

end WNear.Binary.VecWithCap
