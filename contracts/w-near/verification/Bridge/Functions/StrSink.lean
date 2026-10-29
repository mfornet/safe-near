import Bridge.Functions.StrGrow
import Bridge.Functions.FmtSink

/-!
# The `String` sink of `alloc::fmt::format` (846) with room (M8)

846 writes through the `dyn Write` pair `(sp + 4, 1066728)`: `*(sp + 4)` is the address `v` of the
`String` `(ptr, cap, len)`, and the vtable's `write_str` (slot 12, table entry 189) is 840:

```
840 write_str(d, p, k)          spec_extend(*d, p, p + k) (841); Ok (0)
841 spec_extend(v, p, e)        sp -= 32; k = e - p; cap - len ≥ k ⇒ memcpy(ptr + len, p, k) (951);
                                len += k; sp += 32
                                (else finish_grow (845, `StrGrow`) first)
```

`f841_room`, `f840_room`: the room path, `len + k ≤ cap`. Costs (`regular_op_cost`s, activations
excluded): 841 `60 + MemCpy.cost k`, 840 `10` more and 841's activation.
-/

namespace WNear.Binary.StrSink

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.FmtSink (add_sub_left)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `String` at `v` with room, before the write of `k` bytes `sb` at `p`. -/
def roomPre (n g : Nat) (gt : GlobalType) (s v ptr cap len p : UInt32) (ob sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ n ↦[i32][ v.toNat ] ptr ∗ n ↦[i32][ v.toNat + 4 ] cap ∗
    n ↦[i32][ v.toNat + 8 ] len ∗ n ↦[wms][ ptr.toNat + len.toNat ] ob ∗ n ↦[wms][ p.toNat ] sb)

/-- After the write: `len + k`, the bytes copied. -/
def roomPost (n g : Nat) (gt : GlobalType) (s v ptr cap len p k : UInt32) (sb : List UInt8) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 s⟩ ∗ n ↦[i32][ v.toNat ] ptr ∗ n ↦[i32][ v.toNat + 4 ] cap ∗
    n ↦[i32][ v.toNat + 8 ] (len + k) ∗ n ↦[wms][ ptr.toNat + len.toNat ] sb ∗ n ↦[wms][ p.toNat ] sb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`spec_extend(v, p, p + k)`** (841) with room: the `k` bytes at `p` copied after the `len`
bytes, `len + k`. -/
theorem f841_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s v ptr cap len p k : UInt32) (ob sb : List UInt8) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hpc : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f841 Cg
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
  simp only [f841]
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
/-- **`<&mut String as fmt::Write>::write_str(dp, p, k)`** (840, table entry 189) with room: 841 on the
`String` at `*dp`, `Ok`. -/
theorem f840_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType)
    (s dp v ptr cap len p k : UInt32) (ob sb : List UInt8) (hv : v.toNat + 12 ≤ 2 ^ 32)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hpc : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      A 841 ↪[wf] FuncInst.wasm types[31]! inst f841
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f840 Cg
        (fun args => iprop(⌜args = [.i32 dp, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ dp.toNat ] v ∗
          roomPre n g gt s v ptr cap len p ob sb))
        (fun _ => 10 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f841 [.i32 0, .i32 0, .i32 0]) +
          (60 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost))
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ n ↦[i32][ dp.toNat ] v ∗ roomPost n g gt s v ptr cap len p k sb)) := by
  iintro ⟨#Hi, #H951, #H841⟩
  ihave #S841 := f841_room cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s v ptr cap len
    p k ob sb hv hob hsb hroom hpc hp $$ [Hi H951]
  · iframe Hi H951
  have hn := hm.mem
  have ha841 := hm.funcs 841 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hK : 60 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost = K
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hd, HP⟩
  subst hargs
  simp only [f840]
  mstep; mstep [Hd]
  repeat mstep
  mcall S841 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hd HQ
  ipureintro; rw [htype]; rfl

end Spec

end WNear.Binary.StrSink
