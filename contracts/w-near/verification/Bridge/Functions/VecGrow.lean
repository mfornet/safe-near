import Bridge.Functions.AllocWalk581
import Bridge.Functions.DropVec
import Bridge.Functions.VecAppend
import Bridge.Functions.FmtGrow
import Bridge.Functions.BorshFT

/-!
# Growing a nonempty `Vec<u8>` (M5): `__rust_realloc` (312 → 238 → 154) and the grow path of
`write_all` (345)

`VecAppend` appends to the serializer's `Vec<u8>` with room. When the bytes do not fit, the
chain reaches `grow_amortized` (716), which asks `finish_grow` (714) to reallocate the buffer:

```
715 reserve(out, v, len, k)        cap - len < k ⇒ grow_amortized(out, v, len, k) (716)
716 grow_amortized(out, v, len, k) frame 32: c := max(2·cap, len + k, 8); cap ≠ 0 ⇒ the current
                                   memory Some(ptr, cap, align 1) at sp+16;
                                   finish_grow(sp, c, 1, sp+16, sp) (714);
                                   Ok(p, c) ⇒ v.ptr := p, v.cap := c; out := 0 (Ok)
714 finish_grow(out, c, 1, cur, _) frame 16: cur = Some(ptr, cap), cap ≠ 0 ⇒
                                   p := __rust_realloc(ptr, cap, 1, c) (312); p ≠ 0 ⇒ out := (0, p, c)
312, 238                           __rust_realloc → __rg_realloc → 154(&ALLOC, ptr, cap, 1, c)
154 realloc(a, ptr, old, al, new)  p := alloc(a, new, al) (581); memcpy(p, ptr, min(old, new)) (951);
                                   dealloc(a, ptr, old, al) (582); p
```

Here, on `heapInv … F` (any `F`, `AllocWalk581.f581_spec_walk`) with room under the limit:

* `f154_spec` … `f312_spec`: the realloc, the old block's bytes copied to the front of the new
  one, the old block freed (`heapInv … ((p, new) :: live.erase (ptr, old)) (max F 1 + 1)`);
* `f714_spec`, `f716_spec`: `finish_grow` and `grow_amortized` on a nonempty buffer
  (`growCap`: `max (2 · cap) (len + k)`, at least 8);
* `f715_grow` … `f345_grow`: the append chain when the bytes do not fit (`VecAppend`'s room chain
  with the grow), on `growPre2`/`growPost2`: 80 bytes of stack.
-/

namespace WNear.Binary.VecGrow

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor grownLen stk_open581
  stk_close581)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtSink (heapInv_bound add_sub_left)

/-! ## `__rust_realloc` (154, 238, 312) -/

section Realloc

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the realloc (persistent). -/
def reallocCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code310 n maxP inst mi A ∗ dropCode inst mi A ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
    A 154 ↪[wf] FuncInst.wasm types[34]! inst f154 ∗ A 238 ↪[wf] FuncInst.wasm types[33]! inst f238 ∗
    A 312 ↪[wf] FuncInst.wasm types[33]! inst f312)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (reallocCode (GF := GF) n maxP inst mi A) := by
  unfold reallocCode; infer_instance

/-- The heap and the block after the realloc of `(ptr, old)` to `new` bytes at `p`: `bs` (the old
bytes) then `new - old` bytes. -/
def reallocated (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (ptr old new p : UInt32)
    (bs : List UInt8) : IProp GF :=
  iprop(⌜p ≠ 0 ∧ p.toNat + new.toNat < 2 ^ 32⌝ ∗
    (∃ hl', ⌜hl' = hl ∨ hl' = grownLen hl new⌝ ∗
      heapInv n maxP hl' ((p.toNat, new.toNat) :: live.erase (ptr.toNat, old.toNat)) (max F 1 + 1)) ∗
    n ↦[wms][ p.toNat ] bs ∗
    ∃ junk : List UInt8, ⌜junk.length = new.toNat - old.toNat⌝ ∗ n ↦[wms][ p.toNat + old.toNat ] junk)

def preR (n g : Nat) (gt : GlobalType) (s ptr : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP hl live F ∗
    n ↦[wms][ ptr.toNat ] bs)

def postR (n g : Nat) (gt : GlobalType) (s ptr old new : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (p : UInt32) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗
    reallocated n maxP hl live F ptr old new p bs)

def pre154 (n g : Nat) (gt : GlobalType) (s ptr old new : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 1074896, .i32 ptr, .i32 old, .i32 1, .i32 new]⌝ ∗
    preR n g gt s ptr idx ta a578 maxP hl live F bs)

def post154 (n g : Nat) (gt : GlobalType) (s ptr old new : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ postR n g gt s ptr old new idx ta a578 maxP hl live F bs p)

/-- The realloc's cost: the allocation, the copy of the `old` bytes, the free, 154's own 80. -/
def cost154 (cfg : WasmConfig) (F : Nat) (old new : UInt32) : Nat :=
  80 * cfg.regularOpCost + AllocWalk.cost581W cfg F new 1 + MemCpy.cost old.toNat * cfg.regularOpCost +
    224 * cfg.regularOpCost

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`realloc(&ALLOC, ptr, old, 1, new)`** (154) growing a live block (`old < new`): a new block
(581), the `old` bytes copied (951), the old block freed (582). -/
theorem f154_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ptr old new : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (bs : List UInt8) (hs : 16 ≤ s.toNat) (hold : 0 < old.toNat) (hon : old.toNat < new.toNat)
    (hnew : new.toNat < 2 ^ 28) (hbs : bs.length = old.toNat) (hlive : (ptr.toNat, old.toNat) ∈ live)
    (hr : roomFor hl maxP new) :
    reallocCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f154 Cg
        (pre154 n g gt s ptr old new idx ta (A 578) maxP hl live F bs)
        (fun _ => cost154 cfg F old new)
        (post154 n g gt s ptr old new idx ta (A 578) maxP hl live F bs) := by
  iintro #Hk
  iunfold reallocCode at Hk
  icases Hk with ⟨#H310, #Hdr, #H951, -, -, -⟩
  ihave #H310' := H310
  iunfold code310 at H310'
  icases H310' with ⟨-, -, #H581, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  iunfold dropCode at Hdr
  icases Hdr with ⟨-, -, #H582, #H570, #H568, #H576, #H575, -, -, -, -⟩
  obtain ⟨hl0, hl1, hroom, hmax⟩ := hr
  have hn := hm.mem
  have ha581 := hm.funcs 581 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have ha582 := hm.funcs 582 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have t45 : types[45]!.params.length = 4 := by rfl
  have hne : new.toNat ≠ old.toNat := by omega
  unfold cost154
  generalize hM : MemCpy.cost old.toNat * cfg.regularOpCost = M
  generalize hW : AllocWalk.cost581W cfg F new 1 = W
  have S581 := AllocWalk.f581_spec_walk (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm
    (by omega) Cg gt s new 1 idx 0 maxP hl live F
  rw [hW] at S581
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre154, preR at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hbs⟩
  subst hargs
  icases heapInv_bound hlive $$ Hinv with ⟨%hpb, Hinv⟩
  icases stk_open581 n s hs $$ Hs with ⟨%o1, %o2, %o4, %⟨h1, h2, h4⟩, O1, O2, O4, W8⟩
  simp only [f154]
  repeat mstep
  mcall (S581 o1 o2 o4 hs rfl (by decide) (by omega) hnew hl0 hl1 h1 h2 h4 hroom hmax)
    using [Hg O1 O2 O4 Hvt Hinv]
  · iframe Hg O1 O2 O4 Hvt Hinv
  icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, HO, Hvt, %hl', %hhl', Hinv, Hb⟩
  subst hrs
  icases heapInv_bound (p := p.toNat) (s := new.toNat) (by simp) $$ Hinv with ⟨%hqb, Hinv⟩
  have hpz : Numeric.bool (p == 0) = 0 := by
    simp [Numeric.bool]; exact hp0
  repeat mstep
  -- memcpy(p, ptr, min(old, new))
  iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
  isplitr; · (ipureintro; and_intros <;> first | mstep_side | rfl)
  inext; iintro Hc; mstep_post
  have hgt : Numeric.bool (Numeric.irelop32 IRelOp.gt_u old new) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt]; omega
  simp only [hgt, ite_true]
  iunfold block at Hb
  icases Hb with ⟨%cs, %hcs, Hcs⟩
  icases U128From.memBytes_split n p.toNat old.toNat cs (by omega) $$ Hcs with ⟨Hc0, Hc1⟩
  have S951 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg
      (MemCpy.pre n p ptr old (cs.take old.toNat) bs) (fun _ => M) (MemCpy.post n p ptr bs) := by
    rw [← hM]
    exact MemCpy.f951_spec cfg lim (d + 1) types[15]! rfl inst mi n hn Cg p ptr old (cs.take old.toNat) bs
      (by simp; omega) hbs (by omega) (by omega)
  mcall S951 using [Hc0 Hbs]
  · iunfold MemCpy.pre
    iframe Hc0 Hbs
    ipureintro; rfl
  iunfold MemCpy.post at HQ
  icases HQ with ⟨%hrs, Hp, Hbs⟩
  subst hrs
  repeat mstep
  have S582 := AllocDealloc.f582_spec (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi n hn (A 570) (A 568) (A 576) (A 575)
      (hm.funcs 570 (by decide)) (hm.funcs 568 (by decide)) (hm.funcs 576 (by decide)) (hm.funcs 575 (by decide))
      types[32]! types[13]! types[32]! types[0]! rfl rfl rfl rfl rfl rfl rfl rfl (by omega) Cg maxP hl'
      ((p.toNat, new.toNat) :: live) (max F 1) ptr old 1
  iapply mwpi_cons
  iapply mwpi_call'
  isplitr
  · iapply S582
    all_goals (try mpersist)
  isplitr
  · iassumption
  isplitr
  · iassumption
  isplitr
  · ipureintro
    refine ⟨?_, ?_, ?_, ?_⟩
    · assumption
    · mstep_side
    · mstep_side
    · mstep_side
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; mstep_norm_full; omega
  isplitl [Hinv Hbs]
  · mstep_norm_full
    iframe Hinv
    isplitr
    · ipureintro; exact List.mem_cons_of_mem _ hlive
    iunfold block
    iexists bs
    iframe Hbs
    ipureintro; exact hbs
  inext
  iintro %rs Hc HQ
  mstep_post
  icases HQ with ⟨%hrs, Hinv⟩
  subst hrs
  mcredits (5 * cfg.regularOpCost + R)
  repeat mstep
  mcredits R
  iframe Hc
  iunfold post154, postR
  iexists p
  isplitr
  · ipureintro; simp [htype]
  iframe Hg Hvt
  isplitl [HO W8]
  · iapply stk_close581 n s hs
    iframe HO W8
  iunfold reallocated
  isplitr
  · ipureintro; exact ⟨hp0, hqb⟩
  have hel : ((p.toNat, new.toNat) :: live).erase (ptr.toNat, old.toNat) =
      (p.toNat, new.toNat) :: live.erase (ptr.toNat, old.toNat) := by
    rw [List.erase_cons_tail]
    simp only [beq_iff_eq, Prod.mk.injEq, not_and]
    intro _; exact hne
  rw [hel]
  isplitl [Hinv]
  · iexists hl'
    iframe Hinv
    ipureintro
    rcases hhl' with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; rfl)
  iframe Hp
  iexists cs.drop old.toNat
  iframe Hc1
  ipureintro; simp; omega

set_option maxRecDepth 100000 in
/-- `__rg_realloc(ptr, old, 1, new)` (238): `realloc(&ALLOC, …)` (154). -/
theorem f238_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ptr old new : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (bs : List UInt8) (hs : 16 ≤ s.toNat) (hold : 0 < old.toNat) (hon : old.toNat < new.toNat)
    (hnew : new.toNat < 2 ^ 28) (hbs : bs.length = old.toNat) (hlive : (ptr.toNat, old.toNat) ∈ live)
    (hr : roomFor hl maxP new) :
    reallocCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f238 Cg
        (fun args => iprop(⌜args = [.i32 ptr, .i32 old, .i32 1, .i32 new]⌝ ∗
          preR n g gt s ptr idx ta (A 578) maxP hl live F bs))
        (fun _ => 20 * cfg.regularOpCost + cost154 cfg F old new)
        (post154 n g gt s ptr old new idx ta (A 578) maxP hl live F bs) := by
  iintro #Hk
  ihave #S154 := f154_spec (GF := GF) cfg lim (d + 1) types[34]! rfl inst mi A n g ta hm (by omega) Cg gt s ptr
    old new idx maxP hl live F bs hs hold hon hnew hbs hlive hr $$ Hk
  iunfold reallocCode at Hk
  icases Hk with ⟨#H, -, -, #H154, -, -⟩
  iunfold code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have ha154 := hm.funcs 154 (by decide)
  have t34 : types[34]!.params.length = 5 := by rfl
  generalize hK : cost154 cfg F old new = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HP⟩ Hc
  subst hargs
  simp only [f238]
  repeat mstep
  mcall S154 using [HP]
  · iunfold pre154
    iframe HP
    ipureintro; rfl
  iunfold post154 at HQ
  icases HQ with ⟨%p, %hrs, HQ⟩
  subst hrs
  rw [htype]
  mpay
  mcredits R
  iframe Hc
  iunfold post154
  iexists p
  iframe HQ
  ipureintro; rfl

set_option maxRecDepth 100000 in
/-- `__rust_realloc(ptr, old, 1, new)` (312): `__rg_realloc` (238). -/
theorem f312_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 7 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ptr old new : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (bs : List UInt8) (hs : 16 ≤ s.toNat) (hold : 0 < old.toNat) (hon : old.toNat < new.toNat)
    (hnew : new.toNat < 2 ^ 28) (hbs : bs.length = old.toNat) (hlive : (ptr.toNat, old.toNat) ∈ live)
    (hr : roomFor hl maxP new) :
    reallocCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f312 Cg
        (fun args => iprop(⌜args = [.i32 ptr, .i32 old, .i32 1, .i32 new]⌝ ∗
          preR n g gt s ptr idx ta (A 578) maxP hl live F bs))
        (fun _ => 40 * cfg.regularOpCost + cost154 cfg F old new)
        (post154 n g gt s ptr old new idx ta (A 578) maxP hl live F bs) := by
  iintro #Hk
  ihave #S238 := f238_spec (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt s ptr
    old new idx maxP hl live F bs hs hold hon hnew hbs hlive hr $$ Hk
  iunfold reallocCode at Hk
  icases Hk with ⟨#H, -, -, -, #H238, -⟩
  iunfold code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have ha238 := hm.funcs 238 (by decide)
  have t33 : types[33]!.params.length = 4 := by rfl
  generalize hK : cost154 cfg F old new = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, HP⟩ Hc
  subst hargs
  simp only [f312]
  repeat mstep
  mcall S238 using [HP]
  · iframe HP
  iunfold post154 at HQ
  icases HQ with ⟨%p, %hrs, HQ⟩
  subst hrs
  repeat mstep
  rw [htype]
  mcredits R
  iframe Hc
  simp only [Nat.sub_self, List.drop_zero]
  iunfold post154
  iexists p
  iframe HQ
  ipureintro; rfl

end Realloc

/-! ## `finish_grow` (714) and `grow_amortized` (716) on a nonempty buffer -/

section L714

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the grow (persistent): the realloc and 714, 716. -/
def growCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(reallocCode n maxP inst mi A ∗ A 714 ↪[wf] FuncInst.wasm types[39]! inst f714 ∗
    A 716 ↪[wf] FuncInst.wasm types[45]! inst f716)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (growCode (GF := GF) n maxP inst mi A) := by
  unfold growCode; infer_instance

def pre714 (n g : Nat) (gt : GlobalType) (s out c cur x ptr cap : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c, .i32 1, .i32 cur, .i32 x]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 32) 32 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP hl live F ∗
    n ↦[i32][ cur.toNat ] ptr ∗ n ↦[i32][ cur.toNat + 4 ] cap ∗ n ↦[wms][ ptr.toNat ] bs ∗
    n ↦[wms][ out.toNat ] ob)

def post714 (n g : Nat) (gt : GlobalType) (s out c cur ptr cap : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 32) 32 ∗
    vt n 1057464 idx ta a578 ∗ n ↦[i32][ cur.toNat ] ptr ∗ n ↦[i32][ cur.toNat + 4 ] cap ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
    reallocated n maxP hl live F ptr cap c p bs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`finish_grow(out, c, 1, cur, _)`** (714) with the current memory `Some(ptr, cap)`, `cap ≠ 0`:
`__rust_realloc(ptr, cap, 1, c)` (312), `Ok((p, c))` at `out`. -/
theorem f714_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c cur x ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (bs ob : List UInt8) (hs : 32 ≤ s.toNat) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hcur : cur.toNat + 8 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat) (hcc : cap.toNat < c.toNat)
    (hc : c.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat) (hlive : (ptr.toNat, cap.toNat) ∈ live)
    (hr : roomFor hl maxP c) :
    growCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f714 Cg
        (pre714 n g gt s out c cur x ptr cap idx ta (A 578) maxP hl live F bs ob)
        (fun _ => 140 * cfg.regularOpCost + cost154 cfg F cap c)
        (post714 n g gt s out c cur ptr cap idx ta (A 578) maxP hl live F bs) := by
  iintro #Hk
  iunfold growCode at Hk
  icases Hk with ⟨#HR, #H714, #H716⟩
  ihave #S312 := f312_spec (GF := GF) cfg lim (d + 1) types[33]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 16)
    ptr cap c idx maxP hl live F bs (by rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega)
    hcap hcc hc hbs hlive hr $$ HR
  iunfold reallocCode at HR
  icases HR with ⟨#H, -, -, -, -, #H312⟩
  iunfold code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha312 := hm.funcs 312 (by decide)
  have t33 : types[33]!.params.length = 4 := by rfl
  have hlt := s.toNat_lt
  have h16 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_s c 0) = 1 := by
    have h' : c.toNat < 2147483648 := by omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.toIntS, h']
  have hcap0 : cap ≠ 0 := by intro h; subst h; simp at hcap
  have hob0 : (ob.take 4).length = 4 := by simp; omega
  have hob4 : ((ob.drop 4).take 4).length = 4 := by simp; omega
  have hob8 : ((ob.drop 4).drop 4).length = 4 := by simp; omega
  generalize hK : cost154 cfg F cap c = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre714 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp, Hcap, Hbs, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  ihave Ho4 := U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho4
  icases Ho4 with ⟨Ho4, Ho8⟩
  icases stk_split n (s.toNat - 32) 16 16 $$ Hs with ⟨Lo, Fr⟩
  simp only [f714]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hp]
  mstep
  mstep_taken with (simp; exact hptr)
  repeat mstep
  mstep [Hcap]
  mstep
  mstep_taken with (simp; exact hcap0)
  repeat mstep
  mcall S312 using [Hg Lo Hvt Hinv Hbs]
  · iunfold preR
    ihave Lo := stk_addr (show s.toNat - 32 = (s - 16).toNat - 16 by omega) $$ Lo
    iframe Hg Lo Hvt Hinv Hbs
  iunfold post154 at HQ
  icases HQ with ⟨%p, %hrs, HQ⟩
  subst hrs
  iunfold postR at HQ
  icases HQ with ⟨Hg, Lo, Hvt, HA⟩
  iunfold reallocated at HA
  icases HA with ⟨%⟨hp0, hpb⟩, HA⟩
  mcredits (40 * cfg.regularOpCost + R)
  repeat mstep
  repeat mstep
  mstep [Ho4]
  repeat mstep
  mstep [Ho0]
  repeat mstep
  mstep [Ho8]
  repeat mstep
  mstep [Hg]
  rw [show s - 16 + 16 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  iunfold post714
  isplitr
  · ipureintro; rfl
  iexists p
  iframe Hg Hvt Hp Hcap Ho0 Ho4 Ho8
  isplitl [Lo Fr]
  · ihave Lo := stk_addr (show (s - 16).toNat - 16 = s.toNat - 32 by omega) $$ Lo
    iapply stk_join n (s.toNat - 32) 16 16
    iframe Lo Fr
  iunfold reallocated
  iframe HA
  ipureintro; exact ⟨hp0, hpb⟩


/-- The capacity `grow_amortized` asks for: `max (2 · cap) need`, at least 8. -/
def growCap (cap need : UInt32) : UInt32 :=
  if 8 < max (2 * cap.toNat) need.toNat then UInt32.ofNat (max (2 * cap.toNat) need.toNat) else 8

theorem growCap_toNat (cap need : UInt32) (hc : cap.toNat < 2 ^ 30) :
    (growCap cap need).toNat = max (max (2 * cap.toNat) need.toNat) 8 := by
  have := need.toNat_lt
  unfold growCap
  split
  · simp only [UInt32.toNat_ofNat']; omega
  · simp; omega

def pre716 (n g : Nat) (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 64) 64 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP hl live F ∗
    n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[wms][ ptr.toNat ] bs ∗
    n ↦[wms][ out.toNat ] ob)

def post716 (n g : Nat) (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32)
    (ta a578 maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (bs : List UInt8) (_args rs : List Value) :
    IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ p : UInt32, g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 64) 64 ∗
    vt n 1057464 idx ta a578 ∗ n ↦[i32][ vec.toNat ] p ∗ n ↦[i32][ vec.toNat + 4 ] growCap cap (len + k) ∗
    n ↦[i32][ out.toNat ] 0 ∗ reallocated n maxP hl live F ptr cap (growCap cap (len + k)) p bs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`grow_amortized(out, vec, len, k)`** (716) on a nonempty buffer `(ptr, cap)`: the capacity
`growCap cap (len + k)` reallocated (714), `Ok` at `out`. -/
theorem f716_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out vec len k ptr cap : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (bs ob : List UInt8) (hs : 64 ≤ s.toNat) (hob : ob.length = 4)
    (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hptr : ptr ≠ 0) (hcap : 0 < cap.toNat)
    (hcap2 : cap.toNat < 2 ^ 27) (hlk : len.toNat + k.toNat < 2 ^ 28) (hbs : bs.length = cap.toNat)
    (hlive : (ptr.toNat, cap.toNat) ∈ live) (hr : roomFor hl maxP (growCap cap (len + k))) :
    growCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f716 Cg
        (pre716 n g gt s out vec len k ptr cap idx ta (A 578) maxP hl live F bs ob)
        (fun _ => 300 * cfg.regularOpCost + cost154 cfg F cap (growCap cap (len + k)))
        (post716 n g gt s out vec len k ptr cap idx ta (A 578) maxP hl live F bs) := by
  have hlk' : (len + k).toNat = len.toNat + k.toNat := by rw [UInt32.toNat_add]; omega
  have hgc := growCap_toNat cap (len + k) (by omega)
  iintro #Hk
  ihave #Hk' := Hk
  iunfold growCode at Hk'
  icases Hk' with ⟨#HR, #H714, -⟩
  iunfold reallocCode at HR
  icases HR with ⟨#H, -⟩
  iunfold code310 at H
  icases H with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha714 := hm.funcs 714 (by decide)
  have t39 : types[39]!.params.length = 5 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have hcap0 : cap ≠ 0 := by intro h; subst h; simp at hcap
  have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (len + k) len) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk']
  have hsh : (cap <<< (1 % 32)).toNat = 2 * cap.toNat := by
    simp [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hsel1 : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (len + k)) = 0
      then Value.i32 (len + k) else Value.i32 (cap <<< (1 % 32))) =
      Value.i32 (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))) := by
    by_cases h2 : len.toNat + k.toNat < 2 * cap.toNat
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (len + k)) = 1 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk']; omega
      rw [this]; simp only [show (1 : UInt32) ≠ 0 by decide, ite_false, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hsh, UInt32.toNat_ofNat']; omega
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (cap <<< (1 % 32)) (len + k)) = 0 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, hlk']; omega
      rw [this]; simp only [ite_true, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hlk', UInt32.toNat_ofNat']; omega
  have hsel2 : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u
      (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))) 8) = 0
      then Value.i32 8 else Value.i32 (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat)))) =
      Value.i32 (growCap cap (len + k)) := by
    have hm' : (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))).toNat =
        max (2 * cap.toNat) (len.toNat + k.toNat) := by
      rw [UInt32.toNat_ofNat']; omega
    by_cases h8 : 8 < max (2 * cap.toNat) (len.toNat + k.toNat)
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u
          (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))) 8) = 1 := by
        simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, UInt32.lt_iff_toNat_lt, hm']
        simp; omega
      rw [this]; simp only [show (1 : UInt32) ≠ 0 by decide, ite_false, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hgc, hm']; omega
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u
          (UInt32.ofNat (max (2 * cap.toNat) (len.toNat + k.toNat))) 8) = 0 := by
        simp only [Numeric.irelop32, Numeric.bool, gt_iff_lt, UInt32.lt_iff_toNat_lt, hm']
        simp; omega
      rw [this]; simp only [ite_true, Value.i32.injEq]
      apply UInt32.toNat_inj.mp; rw [hgc]; simp; omega
  generalize hK : cost154 cfg F cap (growCap cap (len + k)) = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre716 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hp, Hcap, Hbs, Ho⟩
  subst hargs
  icases stk_split n (s.toNat - 64) 32 32 $$ Hs with ⟨Lo, Hs⟩
  icases stk_split n (s.toNat - 64 + 32) 12 20 $$ Hs with ⟨O7, Hs⟩
  icases stk_split n (s.toNat - 64 + 32 + 12) 4 16 $$ Hs with ⟨G1, Hs⟩
  icases stk_split n (s.toNat - 64 + 32 + 12 + 4) 4 12 $$ Hs with ⟨C0, Hs⟩
  icases stk_split n (s.toNat - 64 + 32 + 12 + 4 + 4) 4 8 $$ Hs with ⟨C4, Hs⟩
  icases stk_split n (s.toNat - 64 + 32 + 12 + 4 + 4 + 4) 4 4 $$ Hs with ⟨C8, G2⟩
  iunfold stk at O7 C0 C4 C8
  icases O7 with ⟨%ob7, %hob7, O7⟩
  icases C0 with ⟨%c0, %hc0, C0⟩
  icases C4 with ⟨%c4, %hc4, C4⟩
  icases C8 with ⟨%c8, %hc8, C8⟩
  ihave O7 := memBytes_addr (show s.toNat - 64 + 32 = (s - 32).toNat by omega) $$ O7
  ihave C0 := memBytes_addr (show s.toNat - 64 + 32 + 12 + 4 = (s - 32).toNat + 16 by omega) $$ C0
  ihave C4 := memBytes_addr (show s.toNat - 64 + 32 + 12 + 4 + 4 = (s - 32).toNat + 20 by omega) $$ C4
  ihave C8 := memBytes_addr (show s.toNat - 64 + 32 + 12 + 4 + 4 + 4 = (s - 32).toNat + 24 by omega) $$ C8
  ihave #S714 := f714_spec (GF := GF) cfg lim (d + 1) types[39]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    (s - 32) (growCap cap (len + k)) (s - 32 + 16) (s - 32) ptr cap idx maxP hl live F bs ob7
    (by omega) hob7 (by omega) (by omega) hptr hcap (by omega) (by omega) hbs hlive hr $$ Hk
  simp only [f716]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
  isplitr; · (ipureintro; and_intros <;> first | mstep_side | rfl)
  inext; iintro Hc; mstep_post
  simp only [hsel1]
  repeat mstep
  iapply mwpi_cons; iapply FmtGrow.mwpi_select'; isplitl [Hc]; · iexact Hc
  isplitr; · (ipureintro; and_intros <;> first | mstep_side | rfl)
  inext; iintro Hc; mstep_post
  simp only [hsel2]
  repeat mstep
  mstep [C8]
  repeat mstep
  mstep [C4]
  repeat mstep
  mstep [Hp]
  mstep [C0]
  repeat mstep
  mcall S714 using [Hg Lo Hvt Hinv C0 C4 Hbs O7]
  · iunfold pre714
    ihave Lo := stk_addr (show s.toNat - 64 = (s - 32).toNat - 32 by omega) $$ Lo
    ihave C0 := memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 16).toNat by omega) $$ C0
    ihave C4 := memBytes_addr (show (s - 32).toNat + 20 = (s - 32 + 16).toNat + 4 by omega) $$ C4
    iframe Hg Lo Hvt Hinv C0 C4 Hbs O7
    ipureintro; rfl
  iunfold post714 at HQ
  icases HQ with ⟨%hrs, %p, Hg, Lo, Hvt, C0, C4, Q0, Q4, Q8, HA⟩
  subst hrs
  mcredits (60 * cfg.regularOpCost + R)
  repeat mstep
  mstep [Q8]
  repeat mstep
  mstep [Q4]
  repeat mstep
  mstep [Q0]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hp]
  repeat mstep
  mstep [Ho]
  repeat mstep
  mstep [Hg]
  rw [show s - 32 + 32 = s by simp]
  repeat mstep
  mcredits R
  iframe Hc
  iunfold post716
  isplitr
  · ipureintro; simp [htype]
  iexists p
  iframe Hg Hvt Hp Hcap HA
  isplitr [Ho]
  · ihave Lo := stk_addr (show (s - 32).toNat - 32 = s.toNat - 64 by omega) $$ Lo
    ihave Q0 := stk_word n _ 0 $$ Q0
    ihave Q4 := stk_word n _ p $$ Q4
    ihave Q8 := stk_word n _ _ $$ Q8
    ihave C0 := stk_word n _ ptr $$ C0
    ihave C4 := stk_word n _ cap $$ C4
    ihave C8 := stk_word n _ 1 $$ C8
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32).toNat + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [Q0 Q4]
    · iframe Q0 Q4
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32).toNat + 8) (k1 := 8) (k2 := 4) (k := 12) rfl rfl $$ [Q Q8]
    · iframe Q Q8
    ihave Q := stkJ (a := (s - 32).toNat) (b := s.toNat - 64 + 32 + 12) (k1 := 12) (k2 := 4) (k := 16) (by omega) rfl $$ [Q G1]
    · iframe Q G1
    ihave C := stkJ (a := (s - 32 + 16).toNat) (b := (s - 32 + 16).toNat + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [C0 C4]
    · iframe C0 C4
    ihave C := stkJ (a := (s - 32 + 16).toNat) (b := (s - 32).toNat + 24) (k1 := 8) (k2 := 4) (k := 12) (by omega) rfl $$ [C C8]
    · iframe C C8
    ihave C := stkJ (a := (s - 32 + 16).toNat) (b := s.toNat - 64 + 32 + 12 + 4 + 4 + 4 + 4) (k1 := 12) (k2 := 4) (k := 16) (by omega) rfl $$ [C G2]
    · iframe C G2
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32 + 16).toNat) (k1 := 16) (k2 := 16) (k := 32) (by omega) rfl $$ [Q C]
    · iframe Q C
    iapply stkJ (a := s.toNat - 64) (b := (s - 32).toNat) (k1 := 32) (k2 := 32) (k := 64) (by omega) rfl
    iframe Lo Q
  iexact Ho

end L714

end WNear.Binary.VecGrow
