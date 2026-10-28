import Bridge.Functions.FmtGrow
import Bridge.Functions.MemCpy

/-!
# The `String` sink of `fmt::write` (M5): `<&mut String as fmt::Write>::write_str` (759)

`core::fmt::write` (872) writes through the `dyn Write` pair `(d, 1065404)`, `d` the address of
a word holding the address `v` of a `String` `(ptr, cap, len)` (words at `v`, `v + 4`, `v + 8`).
Its `write_str` (table 157) is 759:

```
759 write_str(d, p, k)          extend_from_slice(*d, p, k) (757); Ok (0)
757 extend_from_slice(v, p, k)  spec_extend(v, p, p + k) (734)
734 spec_extend(v, p, e)        k = e - p; reserve(v, k) (735);
                                memcpy(v.ptr + v.len, p, k) (951); v.len += k
735 reserve(v, k)               do_reserve_and_handle(v, v.len, k) (768)
768                             frame 16: r = reserve(v, len, k) (775) at sp; handle_reserve(r) (773)
775 reserve(out, v, len, k)     cap - len ≥ k ⇒ out = Ok (0); else grow_amortized (776)
773 handle_reserve(r)           Ok ⇒ return
```

Two cases, each a spec of every function of the chain:

* **room** (`…_room`): `len + k ≤ cap`: no allocation, the `k` bytes copied after the `len`
  bytes, `len + k`; the frame of 768 only (16 bytes of stack);
* **grow** (`…_grow`): the `String` is empty (`cap = len = 0`) and `0 < k < 2^28`, with room
  for the allocation (`roomFor`): `grow_amortized` (776, FmtGrow.lean) allocates
  `newCap 0 k = max k 8` bytes at `q ≠ 0`, the heap invariant gets `(q, newCap 0 k)` live
  (`grown`), the `k` bytes copied to `q`, the rest of the block spare; 112 bytes of stack.

Costs (`regular_op_cost`s, activation excluded, `mc = MemCpy.cost k`):
759 `138 + mc` (room) and `453 + mc` plus the allocator's `costAlloc` (grow).
-/

namespace WNear.Binary.FmtSink

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocZeroed (allocCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word roomFor heapAfter costAlloc grownLen content
  heapAfter_ne stk_addr)
open WNear.Binary.VecWithCap (vecCode2 okF)
open WNear.Binary.FmtGrow (newCap pre776 post776 f776_spec)

/-! ## The code -/

section Code

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code `write_str` (759) runs (persistent). -/
def sinkCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(vecCode2 n maxP inst mi A ∗ A 772 ↪[wf] FuncInst.wasm types[39]! inst f772 ∗
    A 776 ↪[wf] FuncInst.wasm types[45]! inst f776 ∗ A 775 ↪[wf] FuncInst.wasm types[45]! inst f775 ∗
    A 773 ↪[wf] FuncInst.wasm types[0]! inst f773 ∗ A 768 ↪[wf] FuncInst.wasm types[31]! inst f768 ∗
    A 735 ↪[wf] FuncInst.wasm types[14]! inst f735 ∗ A 734 ↪[wf] FuncInst.wasm types[31]! inst f734 ∗
    A 757 ↪[wf] FuncInst.wasm types[31]! inst f757)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (sinkCode (GF := GF) n maxP inst mi A) := by
  unfold sinkCode; infer_instance

end Code

/-! ## The heap after the growth -/

section Heap

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The heap after `grow_amortized` allocated `cap` bytes at `q`. -/
def grown (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (q cap : UInt32) : IProp GF :=
  iprop(∃ hl', ⌜hl' = hl ∨ hl' = grownLen hl cap⌝ ∗ heapInv n maxP hl' ((q.toNat, cap.toNat) :: live) F)

/-- A live block ends below `2^32`. -/
theorem heapInv_bound {n maxP len F : Nat} {live : List (Nat × Nat)} {p s : Nat} (h : (p, s) ∈ live) :
    heapInv (GF := GF) n maxP len live F ⊢ ⌜p + s < 2 ^ 32⌝ ∗ heapInv n maxP len live F := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%H, %⟨hw, hl⟩, H1, H2, H3, H4⟩
  isplitr
  · ipureintro
    obtain ⟨-, c, hc, -, hp, hs⟩ := hw.lives.live_cell p s h
    have hb := hw.geo.bounds c hc
    have := hw.len_lt
    unfold CellM.size at hs
    omega
  iunfold heapInv
  iexists H
  iframe H1 H2 H3 H4
  ipureintro; exact ⟨hw, hl⟩

/-- `heapAfter` of a nonzero size: the block, its bound, and `grown`. -/
theorem heapAfter_grown {n maxP hl : Nat} {live : List (Nat × Nat)} {F : Nat} {q cap : UInt32} (hc : 0 < cap.toNat) :
    heapAfter (GF := GF) n maxP hl live F false cap q ⊢
      ⌜q ≠ 0 ∧ q.toNat + cap.toNat < 2 ^ 32⌝ ∗ block n q.toNat cap.toNat ∗ grown n maxP hl live F q cap := by
  iintro H
  iunfold heapAfter at H
  icases H with ⟨%hl', %h, Hinv, Hb⟩
  have hne : cap.toNat ≠ 0 := by omega
  simp only [hne, ite_false]
  icases heapInv_bound (p := q.toNat) (s := cap.toNat) (by simp) $$ Hinv with ⟨%hb, Hinv⟩
  isplitr
  · ipureintro
    rcases h with ⟨h0, -⟩ | ⟨-, hq, -⟩
    · omega
    · exact ⟨hq, hb⟩
  iunfold content at Hb
  simp only [Bool.false_eq_true, ite_false]
  iframe Hb
  iunfold grown
  iexists hl'
  iframe Hinv
  ipureintro
  rcases h with ⟨h0, -⟩ | ⟨-, -, h⟩
  · omega
  · exact h

end Heap

/-! ## `RawVec::reserve` (775) and `handle_reserve` (773) -/

section L775

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre775r (n : Nat) (out vec len k cap : UInt32) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 vec, .i32 len, .i32 k]⌝ ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
    n ↦[wms][ out.toNat ] ob)

def post775r (n : Nat) (out vec cap : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ out.toNat ] 0)

/-- `reserve(out, vec, len, k)` (775) with room (`len + k ≤ cap`): `Ok` at `out`. -/
theorem f775_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out vec len k cap : UInt32) (ob : List UInt8)
    (hob : ob.length = 4) (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32)
    (hroom : len.toNat + k.toNat ≤ cap.toNat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f775 Cg (pre775r n out vec len k cap ob)
        (fun _ => 10 * cfg.regularOpCost) (post775r n out vec cap) := by
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (cap - len) k) = 1 := by
    have : (cap - len).toNat = cap.toNat - len.toNat := by
      rw [UInt32.toNat_sub_of_le]; simp [UInt32.le_iff_toNat_le]; omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le, this]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre775r at HP
  icases HP with ⟨%hargs, Hcap, Ho⟩
  subst hargs
  simp only [f775]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Ho]
  mcredits R
  iframe Hc
  iunfold post775r
  iframe Hcap Ho
  ipureintro; simp [htype]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `reserve(out, vec, 0, k)` (775) on an empty `RawVec<u8>`, `k > 0`: `grow_amortized` (776). -/
theorem f775_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 11 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec k p0 : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 4) (hs : 96 ≤ s.toNat)
    (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hout : out.toNat + 4 ≤ 2 ^ 32) (hk0 : 0 < k.toNat)
    (hk : k.toNat < 2 ^ 28) (hr : roomFor hl maxP (newCap 0 k)) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    vecCode2 n maxP inst mi A ∗ A 772 ↪[wf] FuncInst.wasm types[39]! inst f772 ∗
      A 776 ↪[wf] FuncInst.wasm types[45]! inst f776
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f775 Cg
        (pre776 n g gt s out vec 0 k p0 idx ta (A 578) maxP hl live F ob)
        (fun _ => 325 * cfg.regularOpCost + costAlloc cfg false (newCap 0 k))
        (post776 n g gt s out vec 0 k idx ta (A 578) maxP hl live F) := by
  iintro ⟨#Hv, #H772, #H776⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #S776 := f776_spec (GF := GF) cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s out vec 0 k p0 idx maxP hl live ob hob hs hvec hout (by simp; omega) hr (F := F) (hF := hF) $$ [Hv H772]
  · iframe Hv H772
  have hn := hm.mem
  have ha776 := hm.funcs 776 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (0 - 0) k) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre776 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp0, Hcap, Ho⟩
  subst hargs
  simp only [f775]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mcall S776 using [Hg Hs Hvt Hinv Hp0 Hcap Ho]
  · iunfold pre776
    iframe Hg Hs Hvt Hinv Hp0 Hcap Ho
    ipureintro; rfl
  repeat mstep
  mcredits R
  iframe Hc
  iunfold post776 at HQ
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  rw [htype]
  iunfold post776
  isplitr
  · ipureintro; rfl
  iexact HQ

/-- `handle_reserve(r)` (773) on `Ok`: returns. -/
theorem f773_ok (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (r : UInt32) (hr : r.toNat + 4 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f773 Cg
        (fun args => iprop(⌜args = [.i32 r]⌝ ∗ n ↦[i32][ r.toNat ] 0))
        (fun _ => 6 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ r.toNat ] 0)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hr⟩
  subst hargs
  simp only [f773]
  repeat mstep
  mstep [Hr]
  repeat mstep
  mcredits R
  iframe Hc Hr

end L775

/-! ## `do_reserve_and_handle` (768) and `reserve` (735) -/

section L768

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `RawVec`'s words in the grow case after the growth: `ptr = q`, `cap`. -/
def rawGrown (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (vec k : UInt32) : IProp GF :=
  iprop(∃ q : UInt32, n ↦[i32][ vec.toNat ] q ∗ n ↦[i32][ vec.toNat + 4 ] newCap 0 k ∗
    heapAfter n maxP hl live F false (newCap 0 k) q)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `do_reserve_and_handle(vec, len, k)` (768) with room. -/
theorem f768_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec len k cap : UInt32) (hs : 16 ≤ s.toNat)
    (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat) :
    A 775 ↪[wf] FuncInst.wasm types[45]! inst f775 ∗ A 773 ↪[wf] FuncInst.wasm types[0]! inst f773 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f768 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat + 4 ] cap))
        (fun _ => 51 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ vec.toNat + 4 ] cap)) := by
  iintro ⟨#H775, #H773, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha775 := hm.funcs 775 (by decide)
  have ha773 := hm.funcs 773 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcap⟩
  subst hargs
  icases stk_split n (s.toNat - 16) 4 12 $$ Hs with ⟨O, U⟩
  iunfold stk at O
  icases O with ⟨%ob, %hob, O⟩
  ihave O := memBytes_addr (show s.toNat - 16 = (s - 16).toNat by omega) $$ O
  simp only [f768]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (f775_room cfg lim (d + 1) types[45]! (by rfl) inst mi n hn Cg (s - 16) vec len k cap ob hob
      (by omega) hvec hroom) using [Hcap O]
  · iunfold pre775r
    iframe Hcap O
    ipureintro; rfl
  iunfold post775r at HQ
  icases HQ with ⟨%hrs, Hcap, O⟩
  subst hrs
  repeat mstep
  mcall (f773_ok cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg (s - 16) (by omega)) using [O]
  · iframe O
  icases HQ with ⟨%hrs, O⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hcap
  ihave O := stk_word n _ 0 $$ O
  ihave O := stk_addr (show (s - 16).toNat = s.toNat - 16 by omega) $$ O
  iapply stk_join n (s.toNat - 16) 4 12
  iframe O U

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `do_reserve_and_handle(vec, 0, k)` (768) on an empty `RawVec<u8>`: the growth. -/
theorem f768_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 12 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec k p0 : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hk0 : 0 < k.toNat)
    (hk : k.toNat < 2 ^ 28) (hr : roomFor hl maxP (newCap 0 k)) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f768 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 0, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F ∗
          n ↦[i32][ vec.toNat ] p0 ∗ n ↦[i32][ vec.toNat + 4 ] 0))
        (fun _ => 366 * cfg.regularOpCost + costAlloc cfg false (newCap 0 k))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
          vt n 1057464 idx ta (A 578) ∗ rawGrown n maxP hl live F vec k)) := by
  iintro #Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, #H772, #H776, #H775, #H773, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha775 := hm.funcs 775 (by decide)
  have ha773 := hm.funcs 773 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp0, Hcap⟩
  subst hargs
  icases stk_split n (s.toNat - 112) 96 16 $$ Hs with ⟨X, Hs⟩
  icases stk_split n (s.toNat - 112 + 96) 4 12 $$ Hs with ⟨O, U⟩
  iunfold stk at O
  icases O with ⟨%ob, %hob, O⟩
  ihave O := memBytes_addr (show s.toNat - 112 + 96 = (s - 16).toNat by omega) $$ O
  ihave X := stk_addr (show s.toNat - 112 = (s - 16).toNat - 96 by omega) $$ X
  ihave #S775 := f775_grow (GF := GF) cfg lim (d + 1) types[45]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt (s - 16) (s - 16) vec k p0 idx maxP hl live ob hob (by omega) hvec (by omega) hk0 hk hr (F := F) (hF := hF) $$ [Hv H772 H776]
  · iframe Hv H772 H776
  simp only [f768]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall S775 using [Hg X Hvt Hinv Hp0 Hcap O]
  · iunfold pre776
    iframe Hg X Hvt Hinv Hp0 Hcap O
    ipureintro; rfl
  iunfold post776 at HQ
  icases HQ with ⟨%hrs, %q, Hg, X, Hvt, Hp0, Hcap, O, HA⟩
  subst hrs
  repeat mstep
  mcall (f773_ok cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg (s - 16) (by omega)) using [O]
  · iframe O
  icases HQ with ⟨%hrs, O⟩
  subst hrs
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hvt
  isplitr [Hp0 Hcap HA]
  · ihave O := stk_word n _ 0 $$ O
    ihave O := stk_addr (show (s - 16).toNat = s.toNat - 112 + 96 by omega) $$ O
    ihave X := stk_addr (show (s - 16).toNat - 96 = s.toNat - 112 by omega) $$ X
    ihave O := stk_join n (s.toNat - 112 + 96) 4 12 $$ [O U]
    · iframe O U
    iapply stk_join n (s.toNat - 112) 96 16
    iframe X O
  iunfold rawGrown
  iexists q
  iframe Hp0 Hcap HA

/-- `reserve(vec, k)` (735) with room: `do_reserve_and_handle(vec, len, k)`. -/
theorem f735_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec len k cap : UInt32) (hs : 16 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f735 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len))
        (fun _ => 66 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len)) := by
  iintro #Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, -, -, #H775, #H773, #H768, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have hn := hm.mem
  have ha768 := hm.funcs 768 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcap, Hlen⟩
  subst hargs
  simp only [f735]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mcall (f768_room cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s vec len k cap
      hs (by omega) hroom) using [Hg Hs Hcap]
  · iframe Hg Hs Hcap
  icases HQ with ⟨%hrs, Hg, Hs, Hcap⟩
  subst hrs
  mcredits R
  iframe Hc Hg Hs Hcap Hlen
  ipureintro; simp [htype]

/-- `reserve(vec, k)` (735) on an empty `RawVec<u8>`: the growth. -/
theorem f735_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 13 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec k p0 : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (hs : 112 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hk0 : 0 < k.toNat)
    (hk : k.toNat < 2 ^ 28) (hr : roomFor hl maxP (newCap 0 k)) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f735 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F ∗
          n ↦[i32][ vec.toNat ] p0 ∗ n ↦[i32][ vec.toNat + 4 ] 0 ∗ n ↦[i32][ vec.toNat + 8 ] 0))
        (fun _ => 381 * cfg.regularOpCost + costAlloc cfg false (newCap 0 k))
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗
          vt n 1057464 idx ta (A 578) ∗ rawGrown n maxP hl live F vec k ∗ n ↦[i32][ vec.toNat + 8 ] 0)) := by
  iintro #Hk
  ihave #S768 := f768_grow (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec k p0 idx maxP hl live hs (by omega) hk0 hk hr (F := F) (hF := hF) $$ Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, -, -, -, -, #H768, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have hn := hm.mem
  have ha768 := hm.funcs 768 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp0, Hcap, Hlen⟩
  subst hargs
  simp only [f735]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mcall S768 using [Hg Hs Hvt Hinv Hp0 Hcap]
  · iframe Hg Hs Hvt Hinv Hp0 Hcap
    ipureintro; rfl
  icases HQ with ⟨%hrs, Hg, Hs, Hvt, HR⟩
  subst hrs
  mcredits R
  iframe Hc Hg Hs Hvt HR Hlen
  ipureintro; simp [htype]

end L768

/-! ## `spec_extend` (734), `extend_from_slice` (757), `write_str` (759) -/

section L734

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Room: the `String` `(ptr, cap, len)` at `vec`, the `k` bytes after its contents. -/
def roomPre (n g : Nat) (gt : GlobalType) (s vec ptr cap len p : UInt32) (ob sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat ] ptr ∗
    n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len ∗
    n ↦[wms][ ptr.toNat + len.toNat ] ob ∗ n ↦[wms][ p.toNat ] sb)

/-- Room, after: `sb` appended, `len + k`. -/
def roomPost (n g : Nat) (gt : GlobalType) (s vec ptr cap len p k : UInt32) (sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat ] ptr ∗
    n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] (len + k) ∗
    n ↦[wms][ ptr.toNat + len.toNat ] sb ∗ n ↦[wms][ p.toNat ] sb)

/-- Grow: the empty `String` at `vec`, the heap. -/
def growPre (n g : Nat) (gt : GlobalType) (s vec p0 p : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    heapInv n maxP hl live F ∗ n ↦[i32][ vec.toNat ] p0 ∗ n ↦[i32][ vec.toNat + 4 ] 0 ∗
    n ↦[i32][ vec.toNat + 8 ] 0 ∗ n ↦[wms][ p.toNat ] sb)

/-- The grown `String` at `vec` holding `sb` (`k` bytes): the block `q` of `newCap 0 k` bytes,
`sb` then spare bytes, live in the heap. -/
def strGrown (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (vec k : UInt32) (sb : List UInt8) : IProp GF :=
  iprop(∃ q : UInt32, ⌜q ≠ 0 ∧ q.toNat + (newCap 0 k).toNat < 2 ^ 32⌝ ∗ n ↦[i32][ vec.toNat ] q ∗
    n ↦[i32][ vec.toNat + 4 ] newCap 0 k ∗ n ↦[i32][ vec.toNat + 8 ] k ∗ n ↦[wms][ q.toNat ] sb ∗
    (∃ rest : List UInt8, ⌜rest.length = (newCap 0 k).toNat - k.toNat⌝ ∗ n ↦[wms][ q.toNat + k.toNat ] rest) ∗
    grown n maxP hl live F q (newCap 0 k))

def growPost (n g : Nat) (gt : GlobalType) (s vec p k : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta a578 ∗
    strGrown n maxP hl live F vec k sb ∗ n ↦[wms][ p.toNat ] sb)

theorem add_sub_left (p k : UInt32) : p + k - p = k := by
  apply UInt32.toNat_inj.mp
  have := p.toNat_lt; have := k.toNat_lt
  rw [UInt32.toNat_sub, UInt32.toNat_add]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `spec_extend(vec, p, p + k)` (734) with room. -/
theorem f734_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec ptr cap len p k : UInt32) (ob sb : List UInt8) (hs : 16 ≤ s.toNat)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f734 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 p, .i32 (p + k)]⌝ ∗ roomPre n g gt s vec ptr cap len p ob sb))
        (fun _ => 106 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ roomPost n g gt s vec ptr cap len p k sb)) := by
  iintro #Hk
  ihave #S735 := f735_room (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec len k cap hs hvec hroom $$ Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, -, -, -, -, -, #H735, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H951 : A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have ha735 := hm.funcs 735 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hpl : (ptr + len).toNat = ptr.toNat + len.toNat := by rw [UInt32.toNat_add]; omega
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  have S951 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg
      (MemCpy.pre n (ptr + len) p k ob sb) (fun _ => M) (MemCpy.post n (ptr + len) p sb) := by
    rw [← hM]
    exact MemCpy.f951_spec cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg (ptr + len) p k ob sb hob hsb
      (by omega) hp
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  iunfold roomPre at HP
  icases HP with ⟨Hg, Hs, Hptr, Hcap, Hlen, Ho, Hsb⟩
  subst hargs
  simp only [f734]
  repeat mstep
  rw [add_sub_left]
  mcall S735 using [Hg Hs Hcap Hlen]
  · iframe Hg Hs Hcap Hlen
  icases HQ with ⟨%hrs, Hg, Hs, Hcap, Hlen⟩
  subst hrs
  repeat mstep
  mstep [Hptr]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  ihave Ho := memBytes_addr (show ptr.toNat + len.toNat = (ptr + len).toNat by omega) $$ Ho
  mcall S951 using [Ho Hsb]
  · iunfold MemCpy.pre
    iframe Ho Hsb
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Ho, Hsb⟩
  subst hrs
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mstep [Hlen]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iunfold roomPost
  iframe Hg Hs Hptr Hcap Hlen Hsb
  iapply memBytes_addr (show (ptr + len).toNat = ptr.toNat + len.toNat by omega) $$ Ho


set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `spec_extend(vec, p, p + k)` (734) on an empty `String`, `0 < k`: the growth, then the copy. -/
theorem f734_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec p0 p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (sb : List UInt8) (hs : 112 ≤ s.toNat) (hsb : sb.length = k.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hk0 : 0 < k.toNat) (hk : k.toNat < 2 ^ 28)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hr : roomFor hl maxP (newCap 0 k)) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f734 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 p, .i32 (p + k)]⌝ ∗
          growPre n g gt s vec p0 p idx ta (A 578) maxP hl live F sb))
        (fun _ => 421 * cfg.regularOpCost + costAlloc cfg false (newCap 0 k) +
          MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ growPost n g gt s vec p k idx ta (A 578) maxP hl live F sb)) := by
  iintro #Hk
  ihave #S735 := f735_grow (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec k p0 idx maxP hl live hs hvec hk0 hk hr (F := F) (hF := hF) $$ Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, -, -, -, -, -, #H735, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  ihave #H951 : A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 $$ []
  · iunfold vecCode2 at Hv
    icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #H, -⟩
    iexact H
  have hn := hm.mem
  have ha735 := hm.funcs 735 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hnc : (newCap 0 k).toNat = max k.toNat 8 := by
    unfold newCap; split <;> simp_all <;> omega
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  iunfold growPre at HP
  icases HP with ⟨Hg, Hs, Hvt, Hinv, Hp0, Hcap, Hlen, Hsb⟩
  subst hargs
  simp only [f734]
  repeat mstep
  rw [add_sub_left]
  mcall S735 using [Hg Hs Hvt Hinv Hp0 Hcap Hlen]
  · iframe Hg Hs Hvt Hinv Hp0 Hcap Hlen
  icases HQ with ⟨%hrs, Hg, Hs, Hvt, HR, Hlen⟩
  subst hrs
  iunfold rawGrown at HR
  icases HR with ⟨%q, Hq, Hcap, HA⟩
  icases heapAfter_grown (by omega) $$ HA with ⟨%⟨hq0, hqb⟩, Hb, Hgr⟩
  iunfold block at Hb
  icases Hb with ⟨%bs, %hbs, Hb⟩
  icases U128From.memBytes_split n q.toNat k.toNat bs (by omega) $$ Hb with ⟨Hb1, Hb2⟩
  have S951 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg
      (MemCpy.pre n (q + 0) p k (bs.take k.toNat) sb) (fun _ => M) (MemCpy.post n (q + 0) p sb) := by
    rw [← hM]
    exact MemCpy.f951_spec cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg (q + 0) p k _ sb
      (by simp; omega) hsb (by simp; omega) hp
  repeat mstep
  mstep [Hq]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  ihave Hb1 := memBytes_addr (show q.toNat = (q + 0).toNat by simp) $$ Hb1
  mcall S951 using [Hb1 Hsb]
  · iunfold MemCpy.pre
    iframe Hb1 Hsb
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Hd, Hsb⟩
  subst hrs
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mstep [Hlen]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iunfold growPost
  iframe Hg Hs Hvt Hsb
  iunfold strGrown
  iexists q
  rw [show UInt32.ofNat 0 + k = k by simp]
  iframe Hq Hcap Hlen Hgr
  isplitr
  · ipureintro; exact ⟨hq0, hqb⟩
  isplitl [Hd]
  · iapply memBytes_addr (show (q + 0).toNat = q.toNat by simp) $$ Hd
  iexists bs.drop k.toNat
  iframe Hb2
  ipureintro; simp; omega


/-- `extend_from_slice(vec, p, k)` (757) with room. -/
theorem f757_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec ptr cap len p k : UInt32) (ob sb : List UInt8) (hs : 16 ≤ s.toNat)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f757 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 p, .i32 k]⌝ ∗ roomPre n g gt s vec ptr cap len p ob sb))
        (fun _ => 122 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ roomPost n g gt s vec ptr cap len p k sb)) := by
  iintro #Hk
  ihave #S734 := f734_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec ptr cap len p k ob sb hs hob hsb hvec hroom hptr hp $$ Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, -, -, -, -, -, -, #H734, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have ha734 := hm.funcs 734 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f757]
  repeat mstep
  mcall S734 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc HQ
  ipureintro; simp [htype]

/-- `extend_from_slice(vec, p, k)` (757) on an empty `String`, `0 < k`. -/
theorem f757_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 15 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec p0 p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (sb : List UInt8) (hs : 112 ≤ s.toNat) (hsb : sb.length = k.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hk0 : 0 < k.toNat) (hk : k.toNat < 2 ^ 28)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hr : roomFor hl maxP (newCap 0 k)) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f757 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 p, .i32 k]⌝ ∗
          growPre n g gt s vec p0 p idx ta (A 578) maxP hl live F sb))
        (fun _ => 437 * cfg.regularOpCost + costAlloc cfg false (newCap 0 k) +
          MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ growPost n g gt s vec p k idx ta (A 578) maxP hl live F sb)) := by
  iintro #Hk
  ihave #S734 := f734_grow (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec p0 p k idx maxP hl live sb hs hsb hvec hk0 hk hp hr (F := F) (hF := hF) $$ Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, -, -, -, -, -, -, #H734, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have ha734 := hm.funcs 734 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  generalize hA : costAlloc cfg false (newCap 0 k) = CA
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f757]
  repeat mstep
  mcall S734 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc HQ
  ipureintro; simp [htype]

/-! ### `write_str` -/

/-- **`<&mut String as fmt::Write>::write_str(dd, p, k)`** (759) with room: `*dd = vec`, the
`k` bytes `sb` at `p` appended to the `String` at `vec`; `Ok`. -/
theorem f759_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s dd vec ptr cap len p k : UInt32) (ob sb : List UInt8) (hs : 16 ≤ s.toNat)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat) (hdd : dd.toNat + 4 ≤ 2 ^ 32)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f759 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
          roomPre n g gt s vec ptr cap len p ob sb))
        (fun _ => 138 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
          roomPost n g gt s vec ptr cap len p k sb)) := by
  iintro #Hk
  ihave #S757 := f757_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec ptr cap len p k ob sb hs hob hsb hvec hroom hptr hp $$ Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, -, -, -, -, -, -, -, #H757⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have hn := hm.mem
  have ha757 := hm.funcs 757 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hdd, HP⟩
  subst hargs
  simp only [f759]
  repeat mstep
  mstep [Hdd]
  repeat mstep
  mcall S757 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hdd HQ
  ipureintro
  match type, htype with
  | ⟨_, [_]⟩, _ => rfl

/-- **`<&mut String as fmt::Write>::write_str(dd, p, k)`** (759) on an empty `String`, `0 < k`:
the growth (`max k 8` bytes), the copy; `Ok`. -/
theorem f759_grow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 16 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s dd vec p0 p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (sb : List UInt8) (hs : 112 ≤ s.toNat) (hsb : sb.length = k.toNat)
    (hdd : dd.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hk0 : 0 < k.toNat)
    (hk : k.toNat < 2 ^ 28) (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hr : roomFor hl maxP (newCap 0 k)) (F : Nat := 1) (hF : okF F := by exact Or.inl rfl) :
    sinkCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f759 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
          growPre n g gt s vec p0 p idx ta (A 578) maxP hl live F sb))
        (fun _ => 453 * cfg.regularOpCost + costAlloc cfg false (newCap 0 k) +
          MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dd.toNat ] vec ∗
          growPost n g gt s vec p k idx ta (A 578) maxP hl live F sb)) := by
  iintro #Hk
  ihave #S757 := f757_grow (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec p0 p k idx maxP hl live sb hs hsb hvec hk0 hk hp hr (F := F) (hF := hF) $$ Hk
  iunfold sinkCode at Hk
  icases Hk with ⟨#Hv, -, -, -, -, -, -, -, #H757⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold vecCode2, allocCode at Hv
    icases Hv with ⟨⟨-, -, -, -, -, -, -, -, -, -, -, #Hi⟩, -⟩
    iexact Hi
  have hn := hm.mem
  have ha757 := hm.funcs 757 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  generalize hA : costAlloc cfg false (newCap 0 k) = CA
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hdd, HP⟩
  subst hargs
  simp only [f759]
  repeat mstep
  mstep [Hdd]
  repeat mstep
  mcall S757 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hdd HQ
  ipureintro
  match type, htype with
  | ⟨_, [_]⟩, _ => rfl

end L734

end WNear.Binary.FmtSink
