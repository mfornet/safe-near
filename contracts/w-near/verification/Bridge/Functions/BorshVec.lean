import Bridge.Functions.VecWithCap
import Bridge.Functions.MemCpy

/-!
# `<[u8]>::to_vec` (374): a fresh `Vec<u8>` holding a copy of a slice

```wat
;; 374 to_vec(out, src, len): 373(out, len)              ;; Vec::with_capacity: (ptr, len, 0)
;;     memcpy(out.ptr, src, len); out.len := len
```

* `f374_spec`: for `0 < len < 2^28` with room for the allocation, the `Vec` `(p, len, len)` at
  `out`, `p` a fresh live block holding the slice (the shape of `ReadRegister.optVecAt`).
-/

namespace WNear.Binary.BorshVec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor grownLen heapAfter content costAlloc)
open WNear.Binary.VecWithCap (vecCode2 pre373 post373 f373_spec)
open WNear.Binary.AllocZeroed (allocCode heapInv_bound)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A plain allocation of `c > 0` bytes, opened: the block's bytes, in bounds. -/
theorem heapAfter_open {n maxP len : Nat} {live : List (Nat × Nat)} {c p : UInt32} (hc : 0 < c.toNat) :
    heapAfter (GF := GF) n maxP len live false c p ⊢
      ∃ bs : List UInt8, ⌜bs.length = c.toNat ∧ p.toNat + c.toNat ≤ 2 ^ 32⌝ ∗ n ↦[wms][ p.toNat ] bs ∗
        ∃ len', ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len c)⌝ ∗
          heapInv n maxP len' ((p.toNat, c.toNat) :: live) 1 := by
  iintro H
  iunfold heapAfter, content at H
  icases H with ⟨%len', %h, H1, H2⟩
  have hc0 : c.toNat ≠ 0 := by omega
  simp only [hc0, Bool.false_eq_true, ite_false]
  iunfold block at H2
  icases H2 with ⟨%bs, %hbs, H2⟩
  ihave H1 := heapInv_bound n maxP len' _ 1 $$ H1
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

/-- A fresh `Vec<u8>` `(p, |data|, |data|)` at `out` holding `data`, `p` live on the heap. -/
def vecAt (n maxP len : Nat) (live : List (Nat × Nat)) (a : Nat) (data : List UInt8) : IProp GF :=
  iprop(∃ p : UInt32, n ↦[i32][ a ] p ∗
    n ↦[i32][ a + 4 ] UInt32.ofNat data.length ∗ n ↦[i32][ a + 8 ] UInt32.ofNat data.length ∗
    ∃ len', ⌜p ≠ 0 ∧ (len' = len ∨ len' = grownLen len (UInt32.ofNat data.length))⌝ ∗
      heapInv n maxP len' ((p.toNat, data.length) :: live) 1 ∗ n ↦[wms][ p.toNat ] data)

def pre374 (n g : Nat) (gt : GlobalType) (s out src c : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (ob sb : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 src, .i32 c]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP len live 1 ∗
    n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ src.toNat ] sb)

def post374 (n g : Nat) (gt : GlobalType) (s out src : UInt32) (idx : UInt32) (ta a578 maxP len : Nat)
    (live : List (Nat × Nat)) (sb : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[wms][ src.toNat ] sb ∗ vecAt n maxP len live out.toNat sb)

/-- The cost of `to_vec` of `c` bytes. -/
def cost374 (cfg : WasmConfig) (c : UInt32) : Nat :=
  33 * cfg.regularOpCost + (35 * cfg.regularOpCost + (203 * cfg.regularOpCost + costAlloc cfg false c)) +
    MemCpy.cost c.toNat * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **`<[u8]>::to_vec`** (374) of the `c` bytes `sb` at `src` (`0 < c < 2^28`, with room): a fresh
`Vec` `(p, c, c)` at `out` holding a copy of `sb`. -/
theorem f374_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out src c : UInt32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob sb : List UInt8) (hob : ob.length = 12) (hsb : sb.length = c.toNat)
    (hs : 80 ≤ s.toNat) (hc0 : 0 < c.toNat) (hc28 : c.toNat < 2 ^ 28) (hr : roomFor len maxP c)
    (hsrc : src.toNat + c.toNat ≤ 2 ^ 32) (hout : out.toNat + 12 ≤ 2 ^ 32) :
    vecCode2 n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f374 Cg
        (pre374 n g gt s out src c idx ta (A 578) maxP len live ob sb)
        (fun _ => cost374 cfg c)
        (post374 n g gt s out src idx ta (A 578) maxP len live sb) := by
  iintro #Hv
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H373 : A 373 ↪[wf] FuncInst.wasm types[14]! inst f373 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  ihave #H951 : A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H⟩
    iexact H
  ihave #S373 := f373_spec (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s out c idx maxP len live ob hob hs hc28 (fun _ => hr) $$ Hv
  have hn := hm.mem
  have ha373 := hm.funcs 373 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre374 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Ho, Hsrc⟩
  subst hargs
  unfold cost374
  generalize hM : MemCpy.cost c.toNat * cfg.regularOpCost = M
  have S951 : ∀ (dst : UInt32) (bs : List UInt8), bs.length = c.toNat → dst.toNat + c.toNat ≤ 2 ^ 32 →
      ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg (MemCpy.pre n dst src c bs sb)
        (fun _ => M) (MemCpy.post n dst src sb) := fun dst bs h1 h2 => by
    rw [← hM]; exact MemCpy.f951_spec cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg dst src c bs sb h1 hsb h2 hsrc
  simp only [f374]
  mstep; mstep
  mcall S373 using [Hg Hs Hvt Hinv Ho]
  · iunfold pre373
    iframe Hg Hs Hvt Hinv Ho
    ipureintro; rfl
  iunfold post373 at HQ
  icases HQ with ⟨%hrs, %p, Hg, Hs, Hvt, O0, O4, O8, HA⟩
  subst hrs
  mcredits (19 * cfg.regularOpCost + M + R)
  icases heapAfter_open hc0 $$ HA with ⟨%bs, %⟨hbs, hpb⟩, Hb, %len', %hl, Hinv⟩
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
  iunfold post374
  iframe Hg Hs Hvt Hsrc
  isplitr
  · ipureintro; simp [htype]
  iunfold vecAt
  iexists p
  have hc : UInt32.ofNat sb.length = c := by
    apply UInt32.toNat_inj.mp; rw [hsb]; simp
  rw [hc, hsb]
  iframe O0 O4 O8
  iexists len'
  iframe Hinv Hb
  ipureintro; exact hl

end Spec

end WNear.Binary.BorshVec
