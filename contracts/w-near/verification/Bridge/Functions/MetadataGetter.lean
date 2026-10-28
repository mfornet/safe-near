import Bridge.Functions.SerdeLeaves
import Bridge.Functions.ResultExpect
import Bridge.Functions.BorshFT
import Bridge.Functions.FtTotalSupply
import Binary.Code.Part06
import Binary.Code.Part13

/-!
# The metadata getter (308) and `String::from(&str)` (771, 763)

```wat
;; 763 from(out, src, k)   766(out, k)                  ;; Vec::with_capacity (94's code): (p, k, 0)
;;                         memcpy(p, src, k); out.len := k
;; 771 from(out, src, k)   763(out, src, k)
;; 308 metadata(out, _)    frame 32 (sp)
;;                         771(out, 1051277, 8)          ;; "ft-1.0.0"                     spec
;;                         771(sp, 1051285, 27)          ;; "Wrapped NEAR fungible token"  name
;;                         771(sp + 16, 1051312, 5)      ;; "wNEAR"                        symbol
;;                         out+72 := 24 (u8); out+60, out+48, out+36 := 0 (three `None`s)
;;                         out+12 .. out+24 := sp .. sp+12; out+24 .. out+36 := sp+16 .. sp+28
```

`FungibleTokenMetadata` is laid out as `spec`, `name`, `symbol` (`String`s, `(ptr, cap, len)`
from 0, 12 and 24), `icon`, `reference` (`Option<String>`, the null pointer for `None`, at 36 and
48), `reference_hash` (`Option<Base64VecU8>`, at 60) and `decimals` (a `u8` at 72); 76 bytes.
The getter builds the three strings by allocating and copying the constants of the data
segment (`metaStrs`, 40 bytes at 1051277).

* `f763_spec`: `String::from` of `0 < k < 2^28` bytes on any free list `F ≥ 1`: a fresh live
  block holding a copy (`strAt`), at `cost763` (`costAllocF`).
* `f308_spec`: the struct (`metaOut`), its strings on the heap (the free list kept), at
  `cost308`.
-/

namespace WNear.Binary.MetadataGetter

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen heapAfter content)
open WNear.Binary.VecWithCap (okG costAllocF vecCode2 pre373 post373)
open WNear.Binary.AllocZeroed (allocCode heapInv_bound)
open WNear.Binary.BorshFT (join64' split64' joinB splitB stkJ stkW stkB stkSp stkA)
open WNear.Binary.BorshInt (stk_bytes')

theorem f766_eq : f766 = f94 := rfl

/-- The three constants: `"ft-1.0.0"`, `"Wrapped NEAR fungible token"`, `"wNEAR"`. -/
def specStr : List UInt8 := [102, 116, 45, 49, 46, 48, 46, 48]
def nameStr : List UInt8 :=
  [87, 114, 97, 112, 112, 101, 100, 32, 78, 69, 65, 82, 32, 102, 117, 110, 103, 105, 98, 108, 101, 32, 116, 111,
    107, 101, 110]
def symbolStr : List UInt8 := [119, 78, 69, 65, 82]

/-- The 40 bytes at 1051277. -/
def metaStrs : List UInt8 := specStr ++ nameStr ++ symbolStr

theorem specStr_length : specStr.length = 8 := rfl
theorem nameStr_length : nameStr.length = 27 := rfl
theorem symbolStr_length : symbolStr.length = 5 := rfl

/-- The heap's room for the getter's three allocations (one page each at most). -/
def Room3 (len maxP : Nat) : Prop :=
  len % 65536 = 0 ∧ 0 < len ∧ len + 3 * 65536 ≤ maxP * 65536 ∧ len + 4 * 65536 ≤ 2 ^ 32

theorem roomFor_of3 {len maxP L : Nat} (size : UInt32) (h : size.toNat ≤ 128) (hr : Room3 len maxP)
    (h1 : len ≤ L) (h2 : L ≤ len + 2 * 65536) (h3 : L % 65536 = 0) : roomFor L maxP size := by
  obtain ⟨r1, r2, r3, r4⟩ := hr
  refine ⟨h3, by omega, ?_, ?_⟩ <;> (rw [FtTotalSupply.cellPages_small size h]; omega)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A plain allocation of `c > 0` bytes on `heapInv … F`, opened: the block's bytes, in bounds. -/
theorem heapAfter_openF {n maxP len : Nat} {live : List (Nat × Nat)} {F : Nat} {c p : UInt32} (hc : 0 < c.toNat) :
    heapAfter (GF := GF) n maxP len live F false c p ⊢
      ∃ bs : List UInt8, ⌜bs.length = c.toNat ∧ p.toNat + c.toNat ≤ 2 ^ 32⌝ ∗ n ↦[wms][ p.toNat ] bs ∗
        ∃ len', ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len c)⌝ ∗
          heapInv n maxP len' ((p.toNat, c.toNat) :: live) F := by
  iintro H
  iunfold heapAfter, content at H
  icases H with ⟨%len', %h, H1, H2⟩
  have hc0 : c.toNat ≠ 0 := by omega
  simp only [hc0, Bool.false_eq_true, ite_false]
  iunfold block at H2
  icases H2 with ⟨%bs, %hbs, H2⟩
  ihave H1 := heapInv_bound n maxP len' _ F $$ H1
  icases H1 with ⟨%⟨hbd, hl32⟩, H1⟩
  have hb := hbd p.toNat c.toNat (by simp)
  iexists bs
  isplitr
  · ipureintro; exact ⟨hbs, by omega⟩
  iframe H2
  iexists len'
  iframe H1
  ipureintro
  rcases h with ⟨h0, -, -⟩ | ⟨-, hp, hl⟩
  · omega
  · exact ⟨hp, hl⟩

/-- The code `String::from` runs (persistent). -/
def strCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(vecCode2 n maxP inst mi A ∗ A 766 ↪[wf] FuncInst.wasm types[14]! inst f766 ∗
    A 763 ↪[wf] FuncInst.wasm types[31]! inst f763 ∗ A 771 ↪[wf] FuncInst.wasm types[31]! inst f771)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (strCode (GF := GF) n maxP inst mi A) := by
  unfold strCode; infer_instance

/-- A fresh `String` `(p, c, c)` at `a` holding `sb`, `p` live on the heap after `len`. -/
def strAt (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (a : Nat) (c : UInt32) (sb : List UInt8) :
    IProp GF :=
  iprop(∃ p : UInt32, n ↦[i32][ a ] p ∗ n ↦[i32][ a + 4 ] c ∗ n ↦[i32][ a + 8 ] c ∗
    ∃ len', ⌜p ≠ 0 ∧ p.toNat + c.toNat ≤ 2 ^ 32 ∧ (len' = len ∨ len' = grownLen len c)⌝ ∗
      heapInv n maxP len' ((p.toNat, c.toNat) :: live) F ∗ n ↦[wms][ p.toNat ] sb)

def pre763 (n g : Nat) (gt : GlobalType) (s out src c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob sb : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 src, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live F ∗
    n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ src.toNat ] sb)

def post763 (n g : Nat) (gt : GlobalType) (s out src c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (sb : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[wms][ src.toNat ] sb ∗ strAt n maxP len live F out.toNat c sb)

/-- The cost of `String::from` of `c` bytes on `heapInv … F`. -/
def cost763 (cfg : WasmConfig) (F : Nat) (c : UInt32) : Nat :=
  33 * cfg.regularOpCost + (35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAllocF cfg F c)) +
    MemCpy.cost c.toNat * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`String::from(&str)`** (763) of the `c` bytes `sb` at `src` (`0 < c < 2^28`, with room), on
any free list `F ≥ 1`: a fresh `String` `(p, c, c)` at `out` holding a copy of `sb`. -/
theorem f763_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out src c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob sb : List UInt8) (hob : ob.length = 12)
    (hsb : sb.length = c.toNat) (hs : 80 ≤ s.toNat) (hc0 : 0 < c.toNat) (hc28 : c.toNat < 2 ^ 28)
    (hr : roomFor len maxP c) (hsrc : src.toNat + c.toNat ≤ 2 ^ 32) (hout : out.toNat + 12 ≤ 2 ^ 32) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f763 Cg
        (pre763 n g gt s out src c idx ta (A 578) maxP len live F ob sb)
        (fun _ => cost763 cfg F c)
        (post763 n g gt s out src c idx ta (A 578) maxP len live F sb) := by
  iintro #Hv
  iunfold strCode at Hv
  icases Hv with ⟨#Hv, #H766, -, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H951 : A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have S94 := SerdeLeaves.f94_spec (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s out c idx maxP len live ob hob hs hc28 (fun _ => hr) F hF
  rw [← f766_eq] at S94
  ihave #S94 := S94 $$ Hv
  have hn := hm.mem
  have ha766 := hm.funcs 766 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre763 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho, Hsrc⟩
  subst hargs
  unfold cost763
  generalize hM : MemCpy.cost c.toNat * cfg.regularOpCost = M
  have S951 : ∀ (dst : UInt32) (bs : List UInt8), bs.length = c.toNat → dst.toNat + c.toNat ≤ 2 ^ 32 →
      ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg (MemCpy.pre n dst src c bs sb)
        (fun _ => M) (MemCpy.post n dst src sb) := fun dst bs h1 h2 => by
    rw [← hM]; exact MemCpy.f951_spec cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg dst src c bs sb h1 hsb h2 hsrc
  simp only [f763]
  mstep; mstep
  mcall S94 using [Hg Hs Hvt Hinv Ho]
  · iunfold pre373
    iframe Hg Hs Hvt Hinv Ho
    ipureintro; rfl
  iunfold post373 at HQ
  icases HQ with ⟨%hrs, %p, Hg, Hs, Hvt, O0, O4, O8, HA⟩
  subst hrs
  mcredits (19 * cfg.regularOpCost + M + R)
  icases heapAfter_openF hc0 $$ HA with ⟨%bs, %⟨hbs, hpb⟩, Hb, %len', %hl, Hinv⟩
  mstep; mstep [O0]; mstep; mstep
  mcall (S951 p bs hbs hpb)
    using [Hb Hsrc]
  · iunfold MemCpy.pre
    iframe Hb Hsrc
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Hb, Hsrc⟩
  subst hrs
  mcredits (4 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep [O8]
  mcredits R
  iframe Hc
  iunfold post763
  iframe Hg Hs Hvt Hsrc
  isplitr
  · ipureintro; simp [htype]
  iunfold strAt
  iexists p
  iframe O0 O4 O8
  iexists len'
  iframe Hinv Hb
  ipureintro; exact ⟨hl.1, hpb, hl.2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`String::from(&str)`** (771): 763. -/
theorem f771_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out src c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (ob sb : List UInt8) (hob : ob.length = 12)
    (hsb : sb.length = c.toNat) (hs : 80 ≤ s.toNat) (hc0 : 0 < c.toNat) (hc28 : c.toNat < 2 ^ 28)
    (hr : roomFor len maxP c) (hsrc : src.toNat + c.toNat ≤ 2 ^ 32) (hout : out.toNat + 12 ≤ 2 ^ 32) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f771 Cg
        (pre763 n g gt s out src c idx ta (A 578) maxP len live F ob sb)
        (fun _ => 20 * cfg.regularOpCost + cost763 cfg F c)
        (post763 n g gt s out src c idx ta (A 578) maxP len live F sb) := by
  iintro #Hk
  ihave #S := f763_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s out src c
    idx maxP len live F hF ob sb hob hsb hs hc0 hc28 hr hsrc hout $$ Hk
  iunfold strCode at Hk
  icases Hk with ⟨#Hv, -, #H763, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have ha763 := hm.funcs 763 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize cost763 cfg F c = C
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre763 at HP
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f771]
  mstep; mstep; mstep
  mcall S using [HP]
  · iunfold pre763
    isplitr
    · ipureintro; rfl
    iexact HP
  iunfold post763 at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc
  iunfold post763
  iframe HQ
  ipureintro; simp [htype]

/-- The struct `FungibleTokenMetadata` the getter leaves at `out`: the three `String`s
`(ps, 8, 8)`, `(pn, 27, 27)`, `(py, 5, 5)`, the three `None`s (their unused words any bytes) and
`decimals = 24` (its padding any bytes). -/
def metaOut (n out : Nat) (ps pn py : UInt32) : IProp GF :=
  iprop(n ↦[i32][ out ] ps ∗ n ↦[i32][ out + 4 ] 8 ∗ n ↦[i32][ out + 8 ] 8 ∗
    n ↦[i32][ out + 12 ] pn ∗ n ↦[i32][ out + 16 ] 27 ∗ n ↦[i32][ out + 20 ] 27 ∗
    n ↦[i32][ out + 24 ] py ∗ n ↦[i32][ out + 28 ] 5 ∗ n ↦[i32][ out + 32 ] 5 ∗
    n ↦[i32][ out + 36 ] 0 ∗ stk n (out + 40) 8 ∗ n ↦[i32][ out + 48 ] 0 ∗ stk n (out + 52) 8 ∗
    n ↦[i32][ out + 60 ] 0 ∗ stk n (out + 64) 8 ∗ n ↦[wms][ out + 72 ] [24] ∗ stk n (out + 73) 3)

/-- The cost of the getter (308) on `heapInv … F`, activation excluded. -/
def cost308 (cfg : WasmConfig) (F : Nat) : Nat :=
  100 * cfg.regularOpCost + (20 * cfg.regularOpCost + cost763 cfg F 8) +
    (20 * cfg.regularOpCost + cost763 cfg F 27) + (20 * cfg.regularOpCost + cost763 cfg F 5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The metadata getter** (308): `metaOut` at `out`, its three strings fresh live blocks
holding the constants, the free list kept; the heap grown by three pages at most. -/
theorem f308_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out x : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (hs : 112 ≤ s.toNat) (hout : out.toNat + 76 ≤ 2 ^ 32)
    (hr : Room3 len maxP) :
    strCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f308 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 x]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live F ∗ stk n out.toNat 76 ∗
          n ↦[wms][ 1051277 ] metaStrs))
        (fun _ => cost308 cfg F)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
          vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1051277 ] metaStrs ∗
          ∃ (ps pn py : UInt32) (len' : Nat), ⌜len ≤ len' ∧ len' ≤ len + 3 * 65536 ∧ len' % 65536 = 0 ∧
            ps ≠ 0 ∧ pn ≠ 0 ∧ py ≠ 0 ∧ ps.toNat + 8 ≤ 2 ^ 32 ∧ pn.toNat + 27 ≤ 2 ^ 32 ∧ py.toNat + 5 ≤ 2 ^ 32⌝ ∗
            metaOut n out.toNat ps pn py ∗
            heapInv n maxP len' ((py.toNat, 5) :: (pn.toNat, 27) :: (ps.toNat, 8) :: live) F ∗
            n ↦[wms][ ps.toNat ] specStr ∗ n ↦[wms][ pn.toNat ] nameStr ∗ n ↦[wms][ py.toNat ] symbolStr)) := by
  iintro #Hk
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have hlt := s.toNat_lt
  have hol := out.toNat_lt
  have e32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by rw [UInt32.toNat_add, e32]; simp; omega
  have o20 : (out + 20).toNat = out.toNat + 20 := by rw [UInt32.toNat_add]; simp; omega
  have o32 : (out + 32).toNat = out.toNat + 32 := by rw [UInt32.toNat_add]; simp; omega
  have e8 : (s - 32 + 8).toNat = s.toNat - 24 := by rw [UInt32.toNat_add, e32]; simp; omega
  have e24 : (s - 32 + 16 + 8).toNat = s.toNat - 8 := by rw [UInt32.toNat_add, e16]; simp; omega
  have hc8 : (8 : UInt32).toNat = 8 := rfl
  have hc27 : (27 : UInt32).toNat = 27 := rfl
  have hc5 : (5 : UInt32).toNat = 5 := rfl
  have ha771 := hm.funcs 771 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hn := hm.mem
  have hg := hm.glob
  ihave #Hk' := Hk
  iunfold strCode at Hk'
  icases Hk' with ⟨#Hv, -, -, #H771⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  unfold cost308
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho, Hstr⟩
  subst hargs
  -- the output's pieces
  icases stkSp 12 64 rfl $$ Ho with ⟨O0, Ho⟩
  icases stkSp 8 56 rfl $$ Ho with ⟨O12, Ho⟩
  icases stkSp 4 52 rfl $$ Ho with ⟨O20, Ho⟩
  icases stkSp 8 44 rfl $$ Ho with ⟨O24, Ho⟩
  icases stkSp 4 40 rfl $$ Ho with ⟨O32, Ho⟩
  icases stkSp 4 36 rfl $$ Ho with ⟨O36, Ho⟩
  icases stkSp 8 28 rfl $$ Ho with ⟨O40, Ho⟩
  icases stkSp 4 24 rfl $$ Ho with ⟨O48, Ho⟩
  icases stkSp 8 16 rfl $$ Ho with ⟨O52, Ho⟩
  icases stkSp 4 12 rfl $$ Ho with ⟨O60, Ho⟩
  icases stkSp 8 4 rfl $$ Ho with ⟨O64, Ho⟩
  icases stkSp 1 3 rfl $$ Ho with ⟨O72, O73⟩
  icases stk_bytes' $$ O0 with ⟨%ob0, %hob0, O0⟩
  icases stk_bytes' $$ O12 with ⟨%ob12, %hob12, O12⟩
  icases stk_bytes' $$ O20 with ⟨%ob20, %hob20, O20⟩
  icases stk_bytes' $$ O24 with ⟨%ob24, %hob24, O24⟩
  icases stk_bytes' $$ O32 with ⟨%ob32, %hob32, O32⟩
  icases stk_bytes' $$ O36 with ⟨%ob36, %hob36, O36⟩
  icases stk_bytes' $$ O48 with ⟨%ob48, %hob48, O48⟩
  icases stk_bytes' $$ O60 with ⟨%ob60, %hob60, O60⟩
  icases stk_bytes' $$ O72 with ⟨%ob72, %hob72, O72⟩
  -- the constants
  iunfold metaStrs at Hstr
  icases splitB (a := 1051277) (b := 1051277 + 8 + 27) (specStr ++ nameStr) symbolStr rfl $$ Hstr with ⟨Hstr, Hy⟩
  icases splitB (a := 1051277) (b := 1051277 + 8) specStr nameStr rfl $$ Hstr with ⟨Hsp, Hna⟩
  -- the stack
  icases stkSp 80 32 rfl $$ Hs with ⟨L80, Hs⟩
  icases stkSp 12 20 rfl $$ Hs with ⟨N0, Hs⟩
  icases stkSp 4 16 rfl $$ Hs with ⟨X12, Hs⟩
  icases stkSp 12 4 rfl $$ Hs with ⟨Y0, X28⟩
  icases stk_bytes' $$ N0 with ⟨%nb, %hnb, N0⟩
  icases stk_bytes' $$ Y0 with ⟨%yb, %hyb, Y0⟩
  simp only [f308]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  -- spec := String::from("ft-1.0.0")
  mstep; mstep; mstep
  ihave L80 := stkA (b := (s - 32).toNat - 80) (by omega) $$ L80
  ihave #S1 := f771_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    out 1051277 8 idx maxP len live F hF ob0 specStr hob0 rfl (by omega) (by decide) (by decide)
    (roomFor_of3 8 (by decide) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) r1) (by decide) (by omega) $$ Hk
  mcall S1 using [Hg L80 Hvt Hinv O0 Hsp]
  · iunfold pre763
    iframe Hg L80 Hvt Hinv O0
    isplitr
    · ipureintro; rfl
    iapply memBytes_addr (by decide) $$ Hsp
  iunfold post763 at HQ
  icases HQ with ⟨%hrs, Hg, L80, Hvt, Hsp, HA⟩
  iunfold strAt at HA
  icases HA with ⟨%ps, S0, S4, S8, %len1, %⟨hps0, hpsb, hl1⟩, Hinv, Hps⟩
  subst hrs
  rw [FtTotalSupply.grownLen_small _ _ (by decide)] at hl1
  -- name := String::from("Wrapped NEAR fungible token")
  mstep; mstep; mstep
  ihave N0 := memBytes_addr (b := (s - 32).toNat) (by omega) $$ N0
  ihave #S2 := f771_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    (s - 32) 1051285 27 idx maxP len1 ((ps.toNat, 8) :: live) F hF nb nameStr hnb rfl (by omega) (by decide)
    (by decide) (roomFor_of3 27 (by decide) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) (by omega)) (by decide)
    (by omega) $$ Hk
  mcall S2 using [Hg L80 Hvt Hinv N0 Hna]
  · iunfold pre763
    iframe Hg L80 Hvt Hinv N0
    isplitr
    · ipureintro; rfl
    iapply memBytes_addr (by decide) $$ Hna
  iunfold post763 at HQ
  icases HQ with ⟨%hrs, Hg, L80, Hvt, Hna, HA⟩
  iunfold strAt at HA
  icases HA with ⟨%pn, N0, N4, N8, %len2, %⟨hpn0, hpnb, hl2⟩, Hinv, Hpn⟩
  subst hrs
  rw [FtTotalSupply.grownLen_small _ _ (by decide)] at hl2
  -- symbol := String::from("wNEAR")
  mstep; mstep; mstep; mstep; mstep
  ihave Y0 := memBytes_addr (b := (s - 32 + 16).toNat) (by omega) $$ Y0
  ihave #S3 := f771_spec (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    (s - 32 + 16) 1051312 5 idx maxP len2 ((pn.toNat, 27) :: (ps.toNat, 8) :: live) F hF yb symbolStr hyb rfl
    (by omega) (by decide) (by decide) (roomFor_of3 5 (by decide) ⟨r1, r2, r3, r4⟩ (by omega) (by omega) (by omega))
    (by decide) (by omega) $$ Hk
  mcall S3 using [Hg L80 Hvt Hinv Y0 Hy]
  · iunfold pre763
    iframe Hg L80 Hvt Hinv Y0
    isplitr
    · ipureintro; rfl
    iapply memBytes_addr (by decide) $$ Hy
  iunfold post763 at HQ
  icases HQ with ⟨%hrs, Hg, L80, Hvt, Hy, HA⟩
  iunfold strAt at HA
  icases HA with ⟨%py, Y0, Y4, Y8, %len3, %⟨hpy0, hpyb, hl3⟩, Hinv, Hpy⟩
  subst hrs
  rw [FtTotalSupply.grownLen_small _ _ (by decide)] at hl3
  -- decimals, the three `None`s
  mstep; mstep; mstep [O72]
  mstep; mstep; mstep [O60]
  mstep; mstep; mstep [O48]
  mstep; mstep; mstep [O36]
  -- name's length word, then its pointer and capacity
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [N8]
  mstep [O20]
  mstep; mstep
  ihave N04 := join64' (a := (s - 32).toNat) (b := (s - 32).toNat + 4) pn 27 rfl $$ [N0 N4]
  · iframe N0 N4
  mstep [N04]
  mstep [O12]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  -- symbol's pointer and capacity, then its length word
  mstep; mstep
  ihave Y04 := join64' (a := (s - 32 + 16).toNat) (b := (s - 32 + 16).toNat + 4) py 5 rfl $$ [Y0 Y4]
  · iframe Y0 Y4
  ihave Y04 := memBytes_addr (b := (s - 32).toNat + 16) (by omega) $$ Y04
  mstep [Y04]
  mstep [O24]
  rw [ResultExpect.bytes64_decode _ (by simp)]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [Y8]
  mstep [O32]
  -- the epilogue
  mstep; mstep; mstep; mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  mcredits R
  iframe Hc Hg Hvt
  isplitl [L80 N04 N8 X12 Y04 Y8 X28]
  · ihave Y8 := stkW (b := s.toNat - 8) _ (by omega) $$ Y8
    ihave X28 := stkA (b := s.toNat - 4) (by omega) $$ X28
    ihave J := stkJ (a := s.toNat - 8) (b := s.toNat - 4) (k1 := 4) (k2 := 4) (k := 8) (by omega) rfl $$ [Y8 X28]
    · iframe Y8 X28
    ihave Y04 := stkB (b := s.toNat - 16) (k := 8) _ (by omega) (by simp [bytes32]) $$ Y04
    ihave J := stkJ (a := s.toNat - 16) (b := s.toNat - 8) (k1 := 8) (k2 := 8) (k := 16) (by omega) rfl $$ [Y04 J]
    · iframe Y04 J
    ihave X12 := stkA (b := s.toNat - 20) (by omega) $$ X12
    ihave J := stkJ (a := s.toNat - 20) (b := s.toNat - 16) (k1 := 4) (k2 := 16) (k := 20) (by omega) rfl $$ [X12 J]
    · iframe X12 J
    ihave N8 := stkW (b := s.toNat - 24) _ (by omega) $$ N8
    ihave J := stkJ (a := s.toNat - 24) (b := s.toNat - 20) (k1 := 4) (k2 := 20) (k := 24) (by omega) rfl $$ [N8 J]
    · iframe N8 J
    ihave N04 := stkB (b := s.toNat - 32) (k := 8) _ (by omega) (by simp [bytes32]) $$ N04
    ihave J := stkJ (a := s.toNat - 32) (b := s.toNat - 24) (k1 := 8) (k2 := 24) (k := 32) (by omega) rfl $$ [N04 J]
    · iframe N04 J
    ihave L80 := stkA (b := s.toNat - 112) (by omega) $$ L80
    iapply stkJ (a := s.toNat - 112) (b := s.toNat - 32) (k1 := 80) (k2 := 32) (k := 112) (by omega) rfl
    iframe L80 J
  isplitl [Hsp Hna Hy]
  · iunfold metaStrs
    ihave Hsp := memBytes_addr (b := 1051277) (by decide) $$ Hsp
    ihave Hna := memBytes_addr (b := 1051277 + specStr.length) (by decide) $$ Hna
    ihave Hy := memBytes_addr (b := 1051277 + (specStr ++ nameStr).length) (by decide) $$ Hy
    ihave H := joinB (a := 1051277) specStr nameStr rfl $$ [Hsp Hna]
    · iframe Hsp Hna
    iapply joinB (a := 1051277) (specStr ++ nameStr) symbolStr rfl
    iframe H Hy
  iexists ps, pn, py, len3
  isplitr
  · ipureintro
    refine ⟨by omega, by omega, by omega, hps0, hpn0, hpy0, by simpa using hpsb, by simpa using hpnb,
      by simpa using hpyb⟩
  iframe Hinv Hps Hpn Hpy
  iunfold metaOut
  ihave O12 := memBytes_addr (b := out.toNat + 12) (by omega) $$ O12
  icases split64' (a := out.toNat + 12) (b := out.toNat + 16) pn 27 (by omega) $$ O12 with ⟨O12, O16⟩
  ihave O24 := memBytes_addr (b := out.toNat + 24) (by omega) $$ O24
  icases split64' (a := out.toNat + 24) (b := out.toNat + 28) py 5 (by omega) $$ O24 with ⟨O24, O28⟩
  ihave O20 := memBytes_addr (b := out.toNat + 20) (by omega) $$ O20
  ihave O32 := memBytes_addr (b := out.toNat + 32) (by omega) $$ O32
  ihave O36 := memBytes_addr (b := out.toNat + 36) (by omega) $$ O36
  ihave O40 := stkA (b := out.toNat + 40) (by omega) $$ O40
  ihave O48 := memBytes_addr (b := out.toNat + 48) (by omega) $$ O48
  ihave O52 := stkA (b := out.toNat + 52) (by omega) $$ O52
  ihave O60 := memBytes_addr (b := out.toNat + 60) (by omega) $$ O60
  ihave O64 := stkA (b := out.toNat + 64) (by omega) $$ O64
  ihave O72 := memBytes_addr (b := out.toNat + 72) (by omega) $$ O72
  ihave O73 := stkA (b := out.toNat + 73) (by omega) $$ O73
  rw [show storeBytes (Value.i32 24) 1 = ([24] : List UInt8) from rfl]
  iframe S0 S4 S8 O12 O16 O20 O24 O28 O32 O36 O40 O48 O52 O60 O64 O72 O73

end Spec

end WNear.Binary.MetadataGetter
