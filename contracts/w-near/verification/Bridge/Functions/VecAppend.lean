import Bridge.Functions.FmtSink
import Binary.Code.Part07
import Binary.Code.Part12
import Binary.Code.Part13

/-!
# Appending to the serializer's `Vec<u8>` with room (M5): `io::Write::write_all` (345)

`serde_json`'s serializer writes through `&mut Vec<u8>`; on `ft_total_supply`'s path the `Vec`
has capacity 128 and never grows. The chain, a copy of FmtSink.lean's room chain:

```
345 write_all(ser, p, k)          extend_from_slice(*ser, p, k) (711)
711 extend_from_slice(v, p, k)    spec_extend(v, p, p + k) (697)
697 spec_extend(v, p, e)          k = e - p; reserve(v, k) (698); memcpy(v.ptr + v.len, p, k) (951);
                                  v.len += k
698 reserve(v, k)                 do_reserve_and_handle(v, v.len, k) (712)
712                               frame 16: reserve(sp, v, len, k) (715); Ok ⇒ return
715 reserve(out, v, len, k)       cap - len ≥ k ⇒ out = Ok (0)
```

Each is specified with room (`len + k ≤ cap`) on FmtSink's `roomPre`/`roomPost`. Costs
(`regular_op_cost`s, activation excluded, `mc = MemCpy.cost k`): 345 `135 + mc`.
-/

namespace WNear.Binary.VecAppend

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.FmtSink (pre775r post775r roomPre roomPost add_sub_left)

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the append chain (persistent). -/
def appCode (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(A 715 ↪[wf] FuncInst.wasm types[45]! inst f715 ∗ A 712 ↪[wf] FuncInst.wasm types[31]! inst f712 ∗
    A 698 ↪[wf] FuncInst.wasm types[14]! inst f698 ∗ A 697 ↪[wf] FuncInst.wasm types[31]! inst f697 ∗
    A 711 ↪[wf] FuncInst.wasm types[31]! inst f711 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
    inst ↪[inst] mi)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (appCode (GF := GF) inst mi A) := by
  unfold appCode; infer_instance

/-- `reserve(out, vec, len, k)` (715) with room: `Ok` at `out`. -/
theorem f715_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out vec len k cap : UInt32) (ob : List UInt8)
    (hob : ob.length = 4) (hout : out.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 8 ≤ 2 ^ 32)
    (hroom : len.toNat + k.toNat ≤ cap.toNat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f715 Cg (pre775r n out vec len k cap ob)
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
  simp only [f715]
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
/-- `do_reserve_and_handle(vec, len, k)` (712) with room. -/
theorem f712_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec len k cap : UInt32) (hs : 16 ≤ s.toNat)
    (hvec : vec.toNat + 8 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat) :
    A 715 ↪[wf] FuncInst.wasm types[45]! inst f715 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f712 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 len, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat + 4 ] cap))
        (fun _ => 44 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ vec.toNat + 4 ] cap)) := by
  iintro ⟨#H715, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha715 := hm.funcs 715 (by decide)
  have t45 : types[45]!.params.length = 4 := by rfl
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
  simp only [f712]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  repeat mstep
  mcall (f715_room cfg lim (d + 1) types[45]! (by rfl) inst mi n hn Cg (s - 16) vec len k cap ob hob
      (by omega) hvec hroom) using [Hcap O]
  · iunfold pre775r
    iframe Hcap O
    ipureintro; rfl
  iunfold post775r at HQ
  icases HQ with ⟨%hrs, Hcap, O⟩
  subst hrs
  repeat mstep
  mstep [O]
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

/-- `reserve(vec, k)` (698) with room: `do_reserve_and_handle(vec, len, k)`. -/
theorem f698_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec len k cap : UInt32) (hs : 16 ≤ s.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat) :
    appCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f698 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 16) 16 ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len))
        (fun _ => 59 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 16) 16 ∗
          n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len)) := by
  iintro #Hk
  iunfold appCode at Hk
  icases Hk with ⟨#H715, #H712, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha712 := hm.funcs 712 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcap, Hlen⟩
  subst hargs
  simp only [f698]
  repeat mstep
  mstep [Hlen]
  repeat mstep
  mcall (f712_room cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt s vec len k cap
      hs (by omega) hroom) using [Hg Hs Hcap]
  · iframe Hg Hs Hcap
  icases HQ with ⟨%hrs, Hg, Hs, Hcap⟩
  subst hrs
  mcredits R
  iframe Hc Hg Hs Hcap Hlen
  ipureintro; simp [htype]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `spec_extend(vec, p, p + k)` (697) with room. -/
theorem f697_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec ptr cap len p k : UInt32) (ob sb : List UInt8) (hs : 16 ≤ s.toNat)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    appCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f697 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 p, .i32 (p + k)]⌝ ∗ roomPre n g gt s vec ptr cap len p ob sb))
        (fun _ => 99 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ roomPost n g gt s vec ptr cap len p k sb)) := by
  iintro #Hk
  ihave #S698 := f698_room (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec len k cap hs hvec hroom $$ Hk
  iunfold appCode at Hk
  icases Hk with ⟨-, -, #H698, -, -, #H951, #Hi⟩
  have hn := hm.mem
  have ha698 := hm.funcs 698 (by decide)
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
  simp only [f697]
  repeat mstep
  rw [add_sub_left]
  mcall S698 using [Hg Hs Hcap Hlen]
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

/-- `extend_from_slice(vec, p, k)` (711) with room. -/
theorem f711_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 4 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s vec ptr cap len p k : UInt32) (ob sb : List UInt8) (hs : 16 ≤ s.toNat)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    appCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f711 Cg
        (fun args => iprop(⌜args = [.i32 vec, .i32 p, .i32 k]⌝ ∗ roomPre n g gt s vec ptr cap len p ob sb))
        (fun _ => 115 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ roomPost n g gt s vec ptr cap len p k sb)) := by
  iintro #Hk
  ihave #S697 := f697_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec ptr cap len p k ob sb hs hob hsb hvec hroom hptr hp $$ Hk
  iunfold appCode at Hk
  icases Hk with ⟨-, -, -, #H697, -, -, #Hi⟩
  have ha697 := hm.funcs 697 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [f711]
  repeat mstep
  mcall S697 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc HQ
  ipureintro; simp [htype]

/-- **`write_all(ser, p, k)`** (345) with room: `*ser = vec`, the `k` bytes `sb` at `p` appended
to the `Vec` at `vec`. -/
theorem f345_room (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (s ser vec ptr cap len p k : UInt32) (ob sb : List UInt8) (hs : 16 ≤ s.toNat)
    (hob : ob.length = k.toNat) (hsb : sb.length = k.toNat) (hser : ser.toNat + 4 ≤ 2 ^ 32)
    (hvec : vec.toNat + 12 ≤ 2 ^ 32) (hroom : len.toNat + k.toNat ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    appCode inst mi A
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f345 Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ n ↦[i32][ ser.toNat ] vec ∗
          roomPre n g gt s vec ptr cap len p ob sb))
        (fun _ => 135 * cfg.regularOpCost + MemCpy.cost k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ ser.toNat ] vec ∗ roomPost n g gt s vec ptr cap len p k sb)) := by
  iintro #Hk
  ihave #S711 := f711_room (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s vec ptr cap len p k ob sb hs hob hsb hvec hroom hptr hp $$ Hk
  iunfold appCode at Hk
  icases Hk with ⟨-, -, -, -, #H711, -, #Hi⟩
  have hn := hm.mem
  have ha711 := hm.funcs 711 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize hM : MemCpy.cost k.toNat * cfg.regularOpCost = M
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hser, HP⟩
  subst hargs
  simp only [f345]
  repeat mstep
  mstep [Hser]
  repeat mstep
  mcall S711 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HQ⟩
  subst hrs
  mcredits R
  iframe Hc Hser HQ
  ipureintro; simp [htype]

end Spec

end WNear.Binary.VecAppend
