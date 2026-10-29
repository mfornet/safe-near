import Bridge.Functions.StrSinkGrow
import Bridge.Functions.AllocWalkHeap
import Bridge.Functions.PanicDisplayArgs
import Bridge.Functions.WriteSink

/-!
# The `String` sink of `PanicPayload::get` (826): 799, 781, 782

`<PanicPayload as BoxMeUp>::get` (826) formats the panic's message into a fresh `String`
`(1, 0, 0)` through the sink `(sp + 36, 1065680)`, whose `write_str` is 799:

```
799 write_str(d, p, k)          spec_extend(*d, p, p + k) (781); Ok (0)
781 spec_extend(v, p, e)        sp -= 32; k = e - p; cap - len ≥ k ⇒ memcpy(ptr + len, p, k) (951);
                                len += k; sp += 32
                                else c := max(2·cap, len + k, 8); cap = 0 ⇒ None at sp + 16;
                                finish_grow(sp, c, 1, sp + 16) (782); Ok(q, c) at sp ⇒ ptr := q,
                                cap := c; then the copy
782 finish_grow(out, c, 1, cur) cur = None, c ≠ 0 ⇒ p := __rust_alloc(c, 1) (310); p ≠ 0 ⇒
                                out := (0, p, c)
```

799, 781 and 782 are 840, 841 and 845 (`StrSink`, `StrSinkGrow`, `StrGrow`) with other callee
indices. Here: `f781_room`/`f799_room` (the room path), `f782_none` (the first allocation, from no
current memory: 310, `AllocWalk.f310_spec_walk`), `f781_first`/`f799_first` (an empty `String`,
`k > 0` bytes: the first allocation, of `max(k, 8)` bytes).

The panic writes into it at most once with `k > 0` bytes, the first time: `gsW` is the writer state
(the empty `String`, or a `String` allocated once holding `w ≠ []`), and `SinkW1` is `SinkW` for the
writes from the empty `String` or of no byte. `sinkW1_get`: `gsW` is one.
-/

namespace WNear.Binary.GetSink

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr cellPages)
open WNear.Binary.AllocAlloc (wordsOf)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr roomFor)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtSink (add_sub_left)
open WNear.Binary.StrSink (roomPre roomPost)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.AllocFresh (MFunSpec_frame)
open WNear.Binary.AllocGen (MFunSpec_cost)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]


/-! ## `finish_grow` (782) from no current memory -/

def pre782 (n g : Nat) (gt : GlobalType) (s out c cur : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 c, .i32 1, .i32 cur]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
    stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗ heapInv n maxP hl live F ∗
    n ↦[i32][ cur.toNat ] 0 ∗ n ↦[wms][ out.toNat ] ob)

def post782 (n g : Nat) (gt : GlobalType) (s out c cur : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ ∃ (p : UInt32) (hl' : Nat), ⌜p ≠ 0 ∧ (hl' = hl ∨ hl' = hl + 65536)⌝ ∗
    g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗ vt n 1057464 idx ta a578 ∗ n ↦[i32][ cur.toNat ] 0 ∗
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
    heapInv n maxP hl' ((p.toNat, c.toNat) :: live) (max F 1) ∗ block n p.toNat c.toNat)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`finish_grow(out, c, 1, cur)`** (782) with no current memory (`*cur = 0`), `0 < c ≤ 65000`:
`__rust_alloc(c, 1)` (310), `Ok((p, c))` at `out`. -/
theorem f782_none (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 6 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s out c cur : UInt32) (idx : UInt32) (maxP hl : Nat) (live : List (Nat × Nat))
    (F : Nat) (ob : List UInt8) (hs : 16 ≤ s.toNat) (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32)
    (hc0 : 0 < c.toNat) (hc : c.toNat ≤ 65000) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl)
    (hroom : hl + 2 * 65536 ≤ 2 ^ 32) (hmax : hl + 65536 ≤ maxP * 65536) :
    code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f782 Cg
        (pre782 n g gt s out c cur idx ta (A 578) maxP hl live F ob)
        (fun _ => 100 * cfg.regularOpCost + AllocWalk.cost310W cfg F c 1)
        (post782 n g gt s out c cur idx ta (A 578) maxP hl live F) := by
  iintro ⟨#H310c, #H310⟩
  have hcp := WriteSink.cellPages_one c hc
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha310 := hm.funcs 310 (by decide)
  have t13 : types[13]!.params.length = 2 := by rfl
  have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_s c 0) = 1 := by
    have h' : c.toNat < 2147483648 := by omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.toIntS, h']
  have hcne : c ≠ 0 := by intro h; subst h; simp at hc0
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre782 at HP
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hinv, Hcur, Ho⟩
  subst hargs
  ihave Ho := U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho
  icases Ho with ⟨Ho0, Ho4⟩
  ihave Ho4 := U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ Ho4
  icases Ho4 with ⟨Ho4, Ho8⟩
  icases stk_split n (s.toNat - 16) 4 12 $$ Hs with ⟨O1, Hs⟩
  icases stk_split n (s.toNat - 16 + 4) 4 8 $$ Hs with ⟨O2, Hs⟩
  icases stk_split n (s.toNat - 16 + 4 + 4) 4 4 $$ Hs with ⟨O3, O4⟩
  iunfold stk at O1 O2 O4
  icases O1 with ⟨%o1, %ho1, O1⟩
  icases O2 with ⟨%o2, %ho2, O2⟩
  icases O4 with ⟨%o4, %ho4, O4⟩
  have S := AllocWalk.f310_spec_walk (GF := GF) cfg lim (d + 1) types[13]! rfl inst mi A n g ta hm
    (by omega) Cg gt s c 1 idx 0 maxP hl live F o1 o2 o4 hs rfl (by decide)
    (by omega) (by omega) hl0 hl1 ho1 ho2 ho4 (by rw [hcp]; omega) (by rw [hcp]; omega)
  generalize hK : AllocWalk.cost310W cfg F c 1 = K at S ⊢
  ihave #S310 := S $$ H310c
  simp only [f782]
  repeat mstep
  mstep [Hcur]
  repeat mstep
  mcall S310 using [Hg O1 O2 O4 Hvt Hinv]
  · iframe Hg Hvt Hinv
    isplitl [O1]; · iapply memBytes_addr _ $$ O1; omega
    isplitl [O2]; · iapply memBytes_addr _ $$ O2; omega
    iapply memBytes_addr _ $$ O4; omega
  icases HQ with ⟨%p, %⟨hrs, hp0, -⟩, Hg, ⟨%b1, %b2, %b4, %⟨hb1, hb2, hb4⟩, B1, B2, B4⟩, Hvt, %hl', %hhl, Hinv, Hb⟩
  subst hrs
  mcredits (20 * cfg.regularOpCost + R)
  repeat mstep
  mstep [Ho4]
  repeat mstep
  mstep [Ho0]
  repeat mstep
  mstep [Ho8]
  mcredits R
  iframe Hc
  iunfold post782
  isplitr
  · ipureintro; rfl
  iexists p, hl'
  iframe Hg Hvt Hcur Ho0 Ho4 Ho8 Hinv Hb
  isplitr
  · ipureintro; refine ⟨hp0, ?_⟩; rw [hcp] at hhl; omega
  ihave B1 := FmtU128.stk_of n _ 4 _ hb1 $$ B1
  ihave B2 := FmtU128.stk_of n _ 4 _ hb2 $$ B2
  ihave B4 := FmtU128.stk_of n _ 4 _ hb4 $$ B4
  ihave H := stk_join n (s.toNat - 16 + 4 + 4) 4 4 $$ [O3 B4]
  · iframe O3; iapply stk_addr _ $$ B4; omega
  ihave H := stk_join n (s.toNat - 16 + 4) 4 8 $$ [B2 H]
  · iframe H; iapply stk_addr _ $$ B2; omega
  iapply stk_join n (s.toNat - 16) 4 12
  iframe H
  iapply stk_addr _ $$ B1; omega


theorem f781_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s v ptr cap len p k : UInt32) (ob sb : List UInt8) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hpc : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f781 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 p, .i32 (p + k)]⌝ ∗ roomPre n g gt s v ptr cap len p ob sb))
        (fun _ => 60 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ roomPost n g gt s v ptr cap len p k sb)) := by
  iintro ⟨#Hi, #H951⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha951 := hm.funcs 951 (by decide)
  have t15 : types[15]!.params.length = 3 := by rfl
  have hpl : (ptr + len).toNat = ptr.toNat + len.toNat := by rw [UInt32.toNat_add]; omega
  have hlt : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (cap - len) k) = 0 := by
    have : (cap - len).toNat = cap.toNat - len.toNat := by
      rw [UInt32.toNat_sub_of_le]; simp [UInt32.le_iff_toNat_le]; omega
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt, this]; omega
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
  icases HP with ⟨Hg, Hptr, Hcap, Hlen, Ho, Hsb⟩
  subst hargs
  simp only [f781]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  rw [add_sub_left, hlt]
  repeat mstep
  mstep [Hptr]
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
  repeat mstep
  rw [show s - 32 + 32 = s by simp]
  mstep [Hg]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp
  iunfold roomPost
  iframe Hg Hptr Hcap Hsb
  isplitl [Hlen]
  · rw [UInt32.add_comm]; iexact Hlen
  iapply memBytes_addr (show (ptr + len).toNat = ptr.toNat + len.toNat by omega) $$ Ho

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`<&mut String as fmt::Write>::write_str(dp, p, k)`** (799) with room: 841 on the
`String` at `*dp`, `Ok`. -/
theorem f799_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s dp v ptr cap len p k : UInt32) (ob sb : List UInt8) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hpc : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      A 781 ↪[wf] FuncInst.wasm types[31]! inst f781
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f799 Cg
        (fun args => iprop(⌜args = [.i32 dp, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ dp.toNat ] v ∗
          roomPre n g gt s v ptr cap len p ob sb))
        (fun _ => 10 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f781 [.i32 0, .i32 0, .i32 0]) +
          (60 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost))
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dp.toNat ] v ∗ roomPost n g gt s v ptr cap len p k sb)) := by
  iintro ⟨#Hi, #H951, #H781⟩
  ihave #S781 := f781_room cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s v ptr cap len
    p k ob sb hv hob hsb hroom hpc hp $$ [Hi H951]
  · iframe Hi H951
  have hn := hm.mem
  have ha781 := hm.funcs 781 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hK : 60 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hd, HP⟩
  subst hargs
  simp only [f799]
  mstep; mstep [Hd]
  repeat mstep
  mcall S781 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hd HQ
  ipureintro; rw [htype]; rfl


/-! ## `spec_extend` (781) on the empty `String`: the first allocation -/

/-- The code of the sink (persistent): 310's, 782, 781, 799 and 951. -/
def getCode (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(code310 n maxP inst mi A ∗ A 310 ↪[wf] FuncInst.wasm types[13]! inst f310 ∗
    A 782 ↪[wf] FuncInst.wasm types[45]! inst f782 ∗ A 781 ↪[wf] FuncInst.wasm types[31]! inst f781 ∗
    A 951 ↪[wf] FuncInst.wasm types[15]! inst f951)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    Persistent (getCode (GF := GF) n maxP inst mi A) := by
  unfold getCode; infer_instance

/-- The first allocation's capacity for `k` bytes: `max(k, 8)`. -/
def firstCap (k : UInt32) : UInt32 := if 8 < k.toNat then k else 8

theorem firstCap_toNat (k : UInt32) : (firstCap k).toNat = max k.toNat 8 := by
  unfold firstCap; split <;> simp_all <;> omega

/-- The empty `String` `(ptr0, 0, 0)` at `v`, the heap, the `k` bytes `sb` at `p`; 48 bytes of stack. -/
def fPre (n g : Nat) (gt : GlobalType) (s v ptr0 p : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta a578 ∗
    heapInv n maxP hl live F ∗ n ↦[i32][ v.toNat ] ptr0 ∗ n ↦[i32][ v.toNat + 4 ] 0 ∗
    n ↦[i32][ v.toNat + 8 ] 0 ∗ n ↦[wms][ p.toNat ] sb)

/-- … after: `sb` in a fresh block of `c` bytes at `q`. -/
def fPost (n g : Nat) (gt : GlobalType) (s v p c : UInt32) (idx : UInt32) (ta a578 maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (sb : List UInt8) : IProp GF :=
  iprop(∃ (q : UInt32) (hl' : Nat) (tail : List UInt8),
    ⌜q ≠ 0 ∧ q.toNat + c.toNat < 2 ^ 32 ∧ (hl' = hl ∨ hl' = hl + 65536) ∧ sb.length + tail.length = c.toNat⌝ ∗
    g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 48) 48 ∗ vt n 1057464 idx ta a578 ∗
    n ↦[i32][ v.toNat ] q ∗ n ↦[i32][ v.toNat + 4 ] c ∗ n ↦[i32][ v.toNat + 8 ] UInt32.ofNat sb.length ∗
    n ↦[wms][ q.toNat ] (sb ++ tail) ∗ heapInv n maxP hl' ((q.toNat, c.toNat) :: live) (max F 1) ∗
    n ↦[wms][ p.toNat ] sb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`spec_extend(v, p, p + k)`** (781) on the empty `String`, `0 < k ≤ 65000`: a block of
`firstCap k` bytes through `finish_grow` (782), then the copy (951). -/
theorem f781_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s v ptr0 p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (sb : List UInt8) (hs : 48 ≤ s.toNat)
    (hv : v.toNat + 12 ≤ 2 ^ 32) (hsb : sb.length = k.toNat) (hk0 : 0 < k.toNat) (hk : k.toNat ≤ 65000)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl)
    (hroom : hl + 2 * 65536 ≤ 2 ^ 32) (hmax : hl + 65536 ≤ maxP * 65536) :
    getCode n maxP inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f781 Cg
        (fun args => iprop(⌜args = [.i32 v, .i32 p, .i32 (p + k)]⌝ ∗
          fPre n g gt s v ptr0 p idx ta (A 578) maxP hl live F sb))
        (fun _ => 300 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost +
          AllocWalk.cost310W cfg F (firstCap k) 1)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ fPost n g gt s v p (firstCap k) idx ta (A 578) maxP hl live F sb)) := by
  have hfc := firstCap_toNat k
  iintro #Hk
  ihave #Hk' := Hk
  iunfold getCode at Hk'
  icases Hk' with ⟨#H310c, #H310, #H782, -, #H951⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha782 := hm.funcs 782 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  have h32 : (s - 32).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have e16 : (s - 32 + 16).toNat = s.toNat - 16 := by simp [UInt32.toNat_add, h32]; omega
  have S782 := f782_none (GF := GF) cfg lim (d + 1) types[45]! rfl inst mi A n g ta hm (by omega) Cg gt (s - 32)
    (s - 32) (firstCap k) (s - 32 + 16) idx maxP hl live F
  have hlt5 : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat 0 - UInt32.ofNat 0) k) = 1 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt]; omega
  have hov : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat 0 + k) (UInt32.ofNat 0)) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt]
  have hsel1 : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((UInt32.ofNat 0) <<< (1 % 32)) (UInt32.ofNat 0 + k)) = 0
      then Value.i32 (UInt32.ofNat 0 + k) else Value.i32 ((UInt32.ofNat 0) <<< (1 % 32))) = Value.i32 k := by
    have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((UInt32.ofNat 0) <<< (1 % 32)) (UInt32.ofNat 0 + k)) = 0 := by
      simp [Numeric.irelop32, Numeric.bool]
    rw [this]; simp
  have hsel2 : (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u k 8) = 0 then Value.i32 8 else Value.i32 k) =
      Value.i32 (firstCap k) := by
    unfold firstCap
    by_cases h8 : 8 < k.toNat
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u k 8) = 1 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt]; omega
      rw [this]; simp [h8]
    · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u k 8) = 0 := by
        simp [Numeric.irelop32, Numeric.bool, UInt32.lt_iff_toNat_lt]; omega
      rw [this]; simp [h8]
  generalize hC : firstCap k = c at hfc S782 hsel2 ⊢
  generalize hK : AllocWalk.cost310W cfg F c 1 = K at S782 ⊢
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  iunfold fPre at HP
  icases HP with ⟨Hg, Hs, Hvt, Hinv, Hp, Hcap, Hlen, Hsb⟩
  icases stk_split n (s.toNat - 48) 16 32 $$ Hs with ⟨Lo, Hs⟩
  icases stk_split n (s.toNat - 48 + 16) 12 20 $$ Hs with ⟨O7, Hs⟩
  icases stk_split n (s.toNat - 48 + 16 + 12) 4 16 $$ Hs with ⟨G1, Hs⟩
  icases stk_split n (s.toNat - 48 + 16 + 12 + 4) 4 12 $$ Hs with ⟨C0, G2⟩
  iunfold stk at O7 C0
  icases O7 with ⟨%ob7, %hob7, O7⟩
  icases C0 with ⟨%c0, %hc0, C0⟩
  ihave O7 := memBytes_addr (show s.toNat - 48 + 16 = (s - 32).toNat by omega) $$ O7
  ihave C0 := memBytes_addr (show s.toNat - 48 + 16 + 12 + 4 = (s - 32).toNat + 16 by omega) $$ C0
  simp only [f781]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  rw [add_sub_left, hlt5]
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
  mstep [C0]
  repeat mstep
  ihave #S782' := S782 ob7 (by omega) hob7 (by omega) (by omega) (by omega) hl0 hl1 hroom hmax $$ [H310c H310]
  · iframe H310c H310
  mcall S782' using [Hg Lo Hvt Hinv C0 O7]
  · iunfold pre782
    ihave Lo := stk_addr (show s.toNat - 48 = (s - 32).toNat - 16 by omega) $$ Lo
    ihave C0 := memBytes_addr (show (s - 32).toNat + 16 = (s - 32 + 16).toNat by omega) $$ C0
    iframe Hg Lo Hvt Hinv C0 O7
    ipureintro; rfl
  iunfold post782 at HQ
  icases HQ with ⟨%hrs, %q, %hl', %⟨hq0, hhl⟩, Hg, Lo, Hvt, C0, Q0, Q4, Q8, Hinv, Hb⟩
  subst hrs
  mcredits (80 * cfg.regularOpCost + M + R)
  repeat mstep
  mstep [Q8]
  repeat mstep
  mstep [Q4]
  repeat mstep
  mstep [Q0]
  repeat mstep
  mstep [Hp]
  repeat mstep
  mstep [Hcap]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  -- the block: its first `k` bytes overwritten
  iunfold block at Hb
  icases Hb with ⟨%bs, %hbs, Hb⟩
  ihave Hinv := FmtSink.heapInv_bound (p := q.toNat) (s := c.toNat) (by simp) $$ Hinv
  icases Hinv with ⟨%hqb, Hinv⟩
  icases U128From.memBytes_split n q.toNat k.toNat bs (by omega) $$ Hb with ⟨Ho, Ht⟩
  have hql : (q + UInt32.ofNat 0).toNat = q.toNat := by simp
  have S951 : ⊢ MFunSpec (GF := GF) cfg lim (d + 1) types[15]! inst mi f951 Cg
      (MemCpy.pre n (q + UInt32.ofNat 0) p k (bs.take k.toNat) sb) (fun _ => M)
      (MemCpy.post n (q + UInt32.ofNat 0) p sb) := by
    rw [← hM]
    exact MemCpy.f951_spec cfg lim (d + 1) types[15]! (by rfl) inst mi n hn Cg (q + UInt32.ofNat 0) p k
      (bs.take k.toNat) sb (by simp; omega) hsb (by omega) hp
  ihave Ho := memBytes_addr (show q.toNat = (q + UInt32.ofNat 0).toNat by omega) $$ Ho
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
  repeat mstep
  rw [show s - 32 + 32 = s by simp]
  mstep [Hg]
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; simp [htype]
  iunfold fPost
  iexists q, hl', bs.drop k.toNat
  iframe Hg Hvt Hp Hcap Hsb Hinv
  isplitr
  · ipureintro; refine ⟨hq0, hqb, hhl, ?_⟩; simp; omega
  isplitl [Lo Q0 Q4 Q8 G1 C0 G2]
  · ihave Lo := stk_addr (show (s - 32).toNat - 16 = s.toNat - 48 by omega) $$ Lo
    ihave Q0 := stk_word n _ 0 $$ Q0
    ihave Q4 := stk_word n _ q $$ Q4
    ihave Q8 := stk_word n _ _ $$ Q8
    ihave C0 := stk_word n _ 0 $$ C0
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32).toNat + 4) (k1 := 4) (k2 := 4) (k := 8) rfl rfl $$ [Q0 Q4]
    · iframe Q0 Q4
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32).toNat + 8) (k1 := 8) (k2 := 4) (k := 12) rfl rfl $$ [Q Q8]
    · iframe Q Q8
    ihave Q := stkJ (a := (s - 32).toNat) (b := s.toNat - 48 + 16 + 12) (k1 := 12) (k2 := 4) (k := 16) (by omega) rfl $$ [Q G1]
    · iframe Q G1
    ihave C := stkJ (a := (s - 32 + 16).toNat) (b := s.toNat - 48 + 16 + 12 + 4 + 4) (k1 := 4) (k2 := 12) (k := 16) (by omega) rfl $$ [C0 G2]
    · iframe C0 G2
    ihave Q := stkJ (a := (s - 32).toNat) (b := (s - 32 + 16).toNat) (k1 := 16) (k2 := 16) (k := 32) (by omega) rfl $$ [Q C]
    · iframe Q C
    iapply stkJ (a := s.toNat - 48) (b := (s - 32).toNat) (k1 := 16) (k2 := 32) (k := 48) (by omega) rfl
    iframe Lo Q
  isplitl [Hlen]
  · iapply (show (n ↦[i32][ v.toNat + 8 ] (UInt32.ofNat 0 + k) : IProp GF) ⊢
        n ↦[i32][ v.toNat + 8 ] UInt32.ofNat sb.length by
      rw [show UInt32.ofNat 0 + k = UInt32.ofNat sb.length by
        apply UInt32.toNat_inj.mp; simp only [UInt32.toNat_add, UInt32.toNat_ofNat']; omega]) $$ Hlen
  ihave Ho := memBytes_addr (show (q + UInt32.ofNat 0).toNat = q.toNat by omega) $$ Ho
  iapply joinB (a := q.toNat) (b := q.toNat + sb.length) sb (bs.drop k.toNat) rfl
  iframe Ho
  iapply memBytes_addr _ $$ Ht; omega



set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`write_str(dp, p, k)`** (799) on the empty `String` at `*dp`, `0 < k ≤ 65000`: the first
allocation (`f781_first`), `Ok`. -/
theorem f799_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s dp v ptr0 p k : UInt32) (idx : UInt32) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F : Nat) (sb : List UInt8) (hs : 48 ≤ s.toNat)
    (hv : v.toNat + 12 ≤ 2 ^ 32) (hsb : sb.length = k.toNat) (hk0 : 0 < k.toNat) (hk : k.toNat ≤ 65000)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (hl0 : hl % 65536 = 0) (hl1 : 0 < hl)
    (hroom : hl + 2 * 65536 ≤ 2 ^ 32) (hmax : hl + 65536 ≤ maxP * 65536) :
    getCode n maxP inst mi A ∗ A 799 ↪[wf] FuncInst.wasm types[15]! inst f799
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f799 Cg
        (fun args => iprop(⌜args = [.i32 dp, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ dp.toNat ] v ∗
          fPre n g gt s v ptr0 p idx ta (A 578) maxP hl live F sb))
        (fun _ => 10 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f781 [.i32 0, .i32 0, .i32 0]) +
          (300 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost +
            AllocWalk.cost310W cfg F (firstCap k) 1))
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dp.toNat ] v ∗
          fPost n g gt s v p (firstCap k) idx ta (A 578) maxP hl live F sb)) := by
  iintro ⟨#Hk, -⟩
  ihave #S781 := f781_first cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s v ptr0
    p k idx maxP hl live F sb hs hv hsb hk0 hk hp hl0 hl1 hroom hmax $$ Hk
  iunfold getCode at Hk
  icases Hk with ⟨#H310c, -, -, #H781, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have ha781 := hm.funcs 781 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hK : 300 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost +
    AllocWalk.cost310W cfg F (firstCap k) 1 = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hd, HP⟩
  subst hargs
  simp only [f799]
  mstep; mstep [Hd]
  repeat mstep
  mcall S781 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hd HQ
  ipureintro; rw [htype]; rfl

/-! ## The sink -/

/-- **A sink for the writes from the empty state or of no byte**: `PanicDisplay.SinkW` with the
extra condition `w = [] ∨ k = 0`. -/
def SinkW1 (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) : IProp GF :=
  iprop(□ ∀ d : Nat, ∀ s : UInt32, ∀ p : UInt32, ∀ k : UInt32, ∀ w : List UInt8, ∀ sb : List UInt8,
    ⌜d ≤ D ∧ 112 ≤ s.toNat ∧ sb.length = k.toNat ∧ p.toNat + k.toNat ≤ 2 ^ 32 ∧ w.length + k.toNat ≤ B ∧
      (w = [] ∨ k.toNat = 0)⌝ -∗
    MFunSpec cfg lim d types[15]! inst mi code Cg
      (fun args => iprop(⌜args = [.i32 data, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 112) 112 ∗ W w ∗ n ↦[wms][ p.toNat ] sb))
      (fun _ => Kw)
      (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        stk n (s.toNat - 112) 112 ∗ W (w ++ sb) ∗ n ↦[wms][ p.toNat ] sb)))

instance (cfg : WasmConfig) (lim : ExecLimits) (D inst : Nat) (mi : ModuleInst) (n g : Nat)
    (gt : GlobalType) (data : UInt32) (code : Func) (W : List UInt8 → IProp GF) (B Kw Cg : Nat) :
    Persistent (SinkW1 cfg lim D inst mi n g gt data code W B Kw Cg) := by
  unfold SinkW1; infer_instance

/-- The `String` at `v` holding `w`: empty `(1, 0, 0)` with the heap as it was, or (`w ≠ []`)
allocated once, `(q, c, |w|)`, live on the heap. -/
def gsW (n maxP hl : Nat) (live : List (Nat × Nat)) (F : Nat) (v idx : UInt32) (ta a578 : Nat)
    (w : List UInt8) : IProp GF :=
  iprop(vt n 1057464 idx ta a578 ∗
    if w = [] then
      n ↦[i32][ v.toNat ] 1 ∗ n ↦[i32][ v.toNat + 4 ] 0 ∗ n ↦[i32][ v.toNat + 8 ] 0 ∗
        heapInv n maxP hl live F
    else
      ∃ (q c : UInt32) (hl' : Nat) (tail : List UInt8),
        ⌜q ≠ 0 ∧ q.toNat + c.toNat < 2 ^ 32 ∧ (hl' = hl ∨ hl' = hl + 65536) ∧ w.length + tail.length = c.toNat⌝ ∗
        n ↦[i32][ v.toNat ] q ∗ n ↦[i32][ v.toNat + 4 ] c ∗ n ↦[i32][ v.toNat + 8 ] UInt32.ofNat w.length ∗
        n ↦[wms][ q.toNat ] (w ++ tail) ∗ heapInv n maxP hl' ((q.toNat, c.toNat) :: live) F)

/-- The worst price of a write on `gsW`. -/
noncomputable def costG (cfg : WasmConfig) (F B : Nat) : Nat :=
  10 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f781 [.i32 0, .i32 0, .i32 0]) +
    (940 * cfg.regularOpCost + MemCpy.cost B * cfg.regularOpCost + AllocWalk.walkCost cfg F +
      cfg.linearOpBaseCost + cfg.linearOpUnitCost)

open WNear.Binary.SerdeStruct (MFunSpec_wrap)

theorem getCode_room (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) :
    getCode (GF := GF) n maxP inst mi A ∗ A 799 ↪[wf] FuncInst.wasm types[15]! inst f799 ⊢
      inst ↪[inst] mi ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
        A 781 ↪[wf] FuncInst.wasm types[31]! inst f781 := by
  iintro ⟨#Hk, -⟩
  iunfold getCode at Hk
  icases Hk with ⟨#H310c, -, -, #H781, #H951⟩
  iunfold code310 at H310c
  icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
  iframe Hi H951 H781

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- 799 on an allocated `gsW`, no byte. -/
theorem gs_room (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F B : Nat) (v idx dd s p : UInt32) (w : List UInt8)
    (hw : w ≠ []) (hwB : w.length ≤ 65000) (hv : v.toNat + 12 ≤ 2 ^ 32) (hp : p.toNat ≤ 2 ^ 32) :
    getCode n maxP inst mi A ∗ A 799 ↪[wf] FuncInst.wasm types[15]! inst f799 ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi f799 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ (n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) w) ∗
          n ↦[wms][ p.toNat ] []))
        (fun _ => costG cfg F B)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ (n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) (w ++ [])) ∗
          n ↦[wms][ p.toNat ] [])) := by
  have hwl : (UInt32.ofNat w.length).toNat = w.length := by
    simp only [UInt32.toNat_ofNat']
    omega
  refine MFunSpec_wrap (α := UInt32 × UInt32 × Nat × List UInt8)
    (fun x => x.1 ≠ 0 ∧ x.1.toNat + x.2.1.toNat < 2 ^ 32 ∧ (x.2.2.1 = hl ∨ x.2.2.1 = hl + 65536) ∧
      w.length + x.2.2.2.length = x.2.1.toNat)
    (P0 := fun x args => iprop(⌜args = [.i32 dd, .i32 p, .i32 0]⌝ ∗ n ↦[i32][ dd.toNat ] v ∗
      roomPre n g gt s v x.1 x.2.1 (UInt32.ofNat w.length) p [] []))
    (Q0 := fun x _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dd.toNat ] v ∗
      roomPost n g gt s v x.1 x.2.1 (UInt32.ofNat w.length) p 0 []))
    (fun x => iprop(stk n (s.toNat - 112) 112 ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[wms][ x.1.toNat ] (w ++ x.2.2.2) ∗ heapInv n maxP x.2.2.1 ((x.1.toNat, x.2.1.toNat) :: live) F)) ?_ ?_ ?_
  · rintro ⟨q, c, hl', tail⟩ ⟨hq0, hqc, hhl, hwt⟩
    simp only at hq0 hqc hhl hwt
    exact (getCode_room n maxP inst mi A).trans
      ((f799_room (GF := GF) cfg lim d types[15]! rfl inst mi A n g ta hm hd Cg gt s dd v q c
        (UInt32.ofNat w.length) p 0 [] [] hv rfl rfl (by simp only [UInt32.reduceToNat]; omega) hqc
        (by simpa using hp)).trans
        (MFunSpec_cost (fun _ => by
          simp only [costG, UInt32.reduceToNat]; rw [show MemCpy.cost 0 = 4 from rfl]; omega)))
  · intro args
    iintro ⟨%ha, Hg, Hs, ⟨Hd, HW⟩, Hp⟩
    iunfold gsW at HW
    simp only [hw, ↓reduceIte]
    icases HW with ⟨Hvt, %q, %c, %hl', %tail, %hx, V0, V4, V8, Hb, Hinv⟩
    iexists (q, c, hl', tail)
    iframe Hs Hvt Hb Hinv
    isplitr; · ipureintro; exact hx
    isplitr; · ipureintro; exact ha
    iframe Hd
    iunfold roomPre
    iframe Hg V0 V4 V8 Hp
    iapply FmtString.memBytes_nil
  · rintro ⟨q, c, hl', tail⟩ ⟨hq0, hqc, hhl, hwt⟩ args rs
    simp only
    iintro ⟨⟨Hs, Hvt, Hb, Hinv⟩, %hrs, Hd, HR⟩
    iunfold roomPost at HR
    icases HR with ⟨Hg, V0, V4, V8, -, Hp⟩
    iframe Hg Hs Hd Hp
    isplitr; · ipureintro; exact hrs
    iunfold gsW
    simp only [List.append_nil, hw, ↓reduceIte]
    iframe Hvt
    iexists q, c, hl', tail
    iframe V0 V4 Hb Hinv
    isplitr; · ipureintro; exact ⟨hq0, hqc, hhl, hwt⟩
    rw [UInt32.add_zero]; iexact V8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- 799 on the empty `gsW`, `0 < k ≤ B ≤ 65000` bytes: the first allocation. -/
theorem gs_first (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (maxP hl : Nat) (live : List (Nat × Nat)) (F B : Nat) (v idx dd s p k : UInt32) (sb : List UInt8)
    (hF : 1 ≤ F) (hs : 112 ≤ s.toNat) (hv : v.toNat + 12 ≤ 2 ^ 32) (hsb : sb.length = k.toNat)
    (hk0 : 0 < k.toNat) (hkB : k.toNat ≤ B) (hB : B ≤ 65000) (hp : p.toNat + k.toNat ≤ 2 ^ 32)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hroom : hl + 2 * 65536 ≤ 2 ^ 32) (hmax : hl + 65536 ≤ maxP * 65536) :
    getCode n maxP inst mi A ∗ A 799 ↪[wf] FuncInst.wasm types[15]! inst f799 ⊢
      MFunSpec (GF := GF) cfg lim d types[15]! inst mi f799 Cg
        (fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ (n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) []) ∗
          n ↦[wms][ p.toNat ] sb))
        (fun _ => costG cfg F B)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗ (n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) ([] ++ sb)) ∗
          n ↦[wms][ p.toNat ] sb)) := by
  have hsbn : sb ≠ [] := by intro h; subst h; simp at hsb; omega
  have hfc := firstCap_toNat k
  have hcp := WriteSink.cellPages_one (firstCap k) (by omega)
  have hmc := StrSinkMulti.memcpy_mono hk0 hkB
  have hFm : max F 1 = F := by omega
  have S := f799_first (GF := GF) cfg lim d types[15]! rfl inst mi A n g ta hm hd Cg gt s dd v 1 p k idx maxP hl
    live F sb (by omega) hv hsb hk0 (by omega) hp hl0 hl1 hroom hmax
  refine S.trans ((MFunSpec_frame (GF := GF) (Fr := iprop(stk n (s.toNat - 112) 64))
    (P' := fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 112) 112 ∗ (n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) []) ∗
      n ↦[wms][ p.toNat ] sb))
    (Q' := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 112) 112 ∗ (n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) ([] ++ sb)) ∗
      n ↦[wms][ p.toNat ] sb)) ?_ ?_).trans (MFunSpec_cost ?_))
  · intro args
    iintro ⟨%ha, Hg, Hs, ⟨Hd, HW⟩, Hp⟩
    iunfold gsW at HW
    simp only [↓reduceIte]
    icases HW with ⟨Hvt, V0, V4, V8, Hinv⟩
    icases stkSp 64 48 rfl $$ Hs with ⟨Hs1, Hs2⟩
    iframe Hs1
    isplitr; · ipureintro; exact ha
    iframe Hd
    iunfold fPre
    iframe Hg Hvt Hinv V0 V4 V8 Hp
    iapply stkA (by omega) $$ Hs2
  · intro args rs
    iintro ⟨Hs1, %hrs, Hd, HP⟩
    iunfold fPost at HP
    icases HP with ⟨%q, %hl', %tail, %⟨hq0, hqc, hhl, hwt⟩, Hg, Hs2, Hvt, V0, V4, V8, Hb, Hinv, Hp⟩
    iframe Hg Hd Hp
    isplitr; · ipureintro; exact hrs
    isplitl [Hs1 Hs2]
    · iapply stkJ (a := s.toNat - 112) (b := s.toNat - 48) (k1 := 64) (k2 := 48) (by omega) rfl
      iframe Hs1
      iapply stkA (by omega) $$ Hs2
    iunfold gsW
    simp only [List.nil_append, hsbn, ↓reduceIte]
    iframe Hvt
    iexists q, firstCap k, hl', tail
    rw [hFm]
    iframe V0 V4 V8 Hb Hinv
    ipureintro; exact ⟨hq0, hqc, hhl, hwt⟩
  · intro _
    simp only [costG, AllocWalk.cost310W, AllocWalk.walkCost, hcp]
    have := Nat.mul_le_mul_right cfg.regularOpCost hmc
    omega


set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **826's `String` is a `SinkW1`**: `*dd = v` and `gsW` at `v`, through 799. -/
theorem sinkW1_get (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (Cg : Nat) (gt : GlobalType) (maxP hl : Nat)
    (live : List (Nat × Nat)) (F B : Nat) (v idx dd : UInt32) (D : Nat) (hD : D + 9 < lim.maxCallDepth)
    (hF : 1 ≤ F) (hB : 1 ≤ B) (hB2 : B ≤ 65000) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (hl0 : hl % 65536 = 0) (hl1 : 0 < hl) (hroom : hl + 2 * 65536 ≤ 2 ^ 32) (hmax : hl + 65536 ≤ maxP * 65536) :
    getCode n maxP inst mi A ∗ A 799 ↪[wf] FuncInst.wasm types[15]! inst f799 ⊢
      SinkW1 (GF := GF) cfg lim D inst mi n g gt dd f799
        (fun w => iprop(n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) w)) B
        (costG cfg F B) Cg := by
  iintro ⟨#Hk, #H799⟩
  ihave #Hk' := Hk
  iunfold getCode at Hk'
  icases Hk' with ⟨#H310c, -, -, #H781, #H951⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  iunfold SinkW1
  imodintro
  iintro %d %s %p %k %w %sb %⟨hdD, hs, hsb, hp, hwB, hwk⟩
  dsimp only
  have hFm : max F 1 = F := by omega
  by_cases hw : w = []
  · subst hw
    by_cases hk : k.toNat = 0
    · -- the empty `String`, no byte
      have hk' : k = 0 := UInt32.toNat_inj.mp (by simpa using hk)
      subst hk'
      have hsb' : sb = [] := List.eq_nil_of_length_eq_zero (by simpa using hsb)
      subst hsb'
      have S := f799_room (GF := GF) cfg lim d types[15]! rfl inst mi A n g ta hm (by omega) Cg gt s dd v 1 0 0 p 0
        [] [] hv rfl rfl (by simp) (by decide) (by simpa using hp)
      have S' := S.trans ((MFunSpec_frame (GF := GF) (Fr := iprop(stk n (s.toNat - 112) 112 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP hl live F))
        (P' := fun args => iprop(⌜args = [.i32 dd, .i32 p, .i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗
          (n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) []) ∗ n ↦[wms][ p.toNat ] []))
        (Q' := fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 112) 112 ∗
          (n ↦[i32][ dd.toNat ] v ∗ gsW n maxP hl live F v idx ta (A 578) ([] ++ [])) ∗ n ↦[wms][ p.toNat ] []))
        (fun args => by
          iintro ⟨%ha, Hg, Hs, ⟨Hd, HW⟩, Hp⟩
          iunfold gsW at HW
          simp only [↓reduceIte]
          icases HW with ⟨Hvt, P0, P4, P8, Hinv⟩
          iframe Hs Hvt Hinv
          isplitr; · ipureintro; exact ha
          iframe Hd
          iunfold roomPre
          iframe Hg P0 P4 P8 Hp
          iapply FmtString.memBytes_nil)
        (fun args rs => by
          iintro ⟨⟨Hs, Hvt, Hinv⟩, %hrs, Hd, HR⟩
          iunfold roomPost at HR
          icases HR with ⟨Hg, P0, P4, P8, -, Hp⟩
          iframe Hg Hs Hd Hp
          isplitr; · ipureintro; exact hrs
          iunfold gsW
          simp only [List.append_nil, ↓reduceIte]
          iframe Hvt Hinv P4 P0
          rw [show (0 : UInt32) + 0 = 0 from rfl]; iexact P8)).trans
        (MFunSpec_cost (K' := fun _ => costG cfg F B) (fun _ => by
          simp only [costG, UInt32.reduceToNat]; rw [show MemCpy.cost 0 = 4 from rfl]; omega)))
      iapply S'
      iframe Hi H951 H781
    · -- the empty `String`, the first allocation
      iapply gs_first cfg lim d inst mi A n g ta hm (by omega) Cg gt maxP hl live F B v idx dd s p k sb hF hs hv
        hsb (by omega) (by simpa using hwB) hB2 hp hl0 hl1 hroom hmax
      iframe Hk H799
  · -- an allocated `String`, no byte
    have hk : k.toNat = 0 := hwk.resolve_left hw
    have hk' : k = 0 := UInt32.toNat_inj.mp (by simpa using hk)
    subst hk'
    have hsb' : sb = [] := List.eq_nil_of_length_eq_zero (by simpa using hsb)
    subst hsb'
    iapply gs_room cfg lim d inst mi A n g ta hm (by omega) Cg gt maxP hl live F B v idx dd s p w hw
      (by simp at hwB; omega) hv (by have := p.toNat_lt; omega)
    iframe Hk H799


end Spec

end WNear.Binary.GetSink
