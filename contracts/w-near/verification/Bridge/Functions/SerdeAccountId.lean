import Bridge.Functions.SerdeDeStr
import Bridge.Functions.AccountIdValid

/-!
# `ValidAccountId::deserialize` (169) on the accepting path (M6)

```wat
;; 169 deserialize(out, de)     a 48-byte frame
r := String::deserialize(de)    ;; 379 → 380
Err(e) → out := Err(e)          ;; 617 is the identity
Ok(s)  → v := ValidAccountId::try_from(s) (501 → 502)
         Ok(v)  → out := Ok(v)
         Err(e) → to_string (130), Error::custom (387), drop (151)   ;; not covered here
;; 501 try_into(out, s)          502 on a copy of the String
;; 502 try_from(out, s)          (p, n) := as_str(s) (779); is_valid_account_id(p, n) (554)
;;                               true → out := Ok(s); false → a Box<dyn Error> (693), drop s (479)
```

* `f779_s`, `f502_valid`, `f501_valid`: `try_from` on a `String` whose bytes are a valid account id:
  `Ok(s)`, the `String` moved.
* `f379_s`: `String::deserialize`, 380's specification (`SerdeDeStr.f380_s`) through the wrapper.
* `f169_s`: from the reader's index, `Ok(ValidAccountId)` holding `body` in a fresh block when 380
  accepts (`ok380`); `Err(box)` when 380 fails. The case of a decoded string that is not a valid
  account id (the custom error's formatting) is excluded by a hypothesis.
-/

namespace WNear.Binary.SerdeAccountId

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr roomFor
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.SerdeRead (rd wsLen)
open WNear.Binary.SerdeErrBox (costErr heapA roomFor4)
open WNear.Binary.SerdeString (heapS cost618)
open WNear.Binary.ParseStr (escTable plain ok646 cost646)
open WNear.Binary.FromUtf8Gen (utf8Width)
open WNear.Binary.SerdeDeStr (code380 ok380 res380 cost380 f380_s)
open WNear.Binary.AccountIdValid (cost554 f554_spec)

section L502

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`String::as_str(out, s)`** (779): `(ptr, len)` at `out`. -/
theorem f779_s (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out s p c m : UInt32) (o0 o4 : List UInt8)
    (h0 : o0.length = 4) (h4 : o4.length = 4) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f779 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 s]⌝ ∗ n ↦[i32][ s.toNat ] p ∗ n ↦[i32][ s.toNat + 4 ] c ∗
          n ↦[i32][ s.toNat + 8 ] m ∗ n ↦[wms][ out.toNat ] o0 ∗ n ↦[wms][ out.toNat + 4 ] o4))
        (fun _ => 12 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ s.toNat ] p ∗ n ↦[i32][ s.toNat + 4 ] c ∗
          n ↦[i32][ s.toNat + 8 ] m ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] m)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, S0, S4, S8, O0, O4⟩
  subst hargs
  simp only [f779]
  mstep; mstep; mstep [S8]; mstep [O4]
  mstep; mstep; mstep [S0]; mstep [O0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe S0 S4 S8 O0 O4

end L502

end WNear.Binary.SerdeAccountId

namespace WNear.Binary.SerdeAccountId

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AccountIdValid (cost554 f554_spec)


section L502v

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`ValidAccountId::try_from(out, s)`** (502) on a `String` `(p, c, m)` whose bytes are a valid
account id: `Ok(s)`, `(0, p, c, m)` at `out`. -/
theorem f502_valid (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a673 a554 a779 : Nat)
    (ha673 : mi.funcAddrs[673]? = some a673) (ha554 : mi.funcAddrs[554]? = some a554)
    (ha779 : mi.funcAddrs[779]? = some a779) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out s p c m : UInt32) (ob bs : List UInt8) (hob : ob.length = 16)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hs : s.toNat + 12 ≤ 2 ^ 32) (hbs : bs.length = m.toNat)
    (hp : p.toNat + m.toNat ≤ 2 ^ 32) (hsp : 48 ≤ sp.toNat) (hv : validAccountIdBytes bs = true) :
    a673 ↪[wf] FuncInst.wasm types[31]! inst f673 ∗ a554 ↪[wf] FuncInst.wasm types[13]! inst f554 ∗
      a779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f502 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 s]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 48) 48 ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[i32][ s.toNat ] p ∗ n ↦[i32][ s.toNat + 4 ] c ∗
          n ↦[i32][ s.toNat + 8 ] m ∗ n ↦[wms][ p.toNat ] bs))
        (fun _ => (120 + cost554 m.toNat) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 48) 48 ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] m ∗ n ↦[i32][ s.toNat ] p ∗ n ↦[i32][ s.toNat + 4 ] c ∗
          n ↦[i32][ s.toNat + 8 ] m ∗ n ↦[wms][ p.toNat ] bs)) := by
  iintro ⟨#F673, #F554, #F779, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, S0, S4, S8, Hb⟩
  subst hargs
  have t13 : types[13]!.params.length = 2 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 48) 16 32 $$ Hs with ⟨S16, Hs⟩
  rw [show sp.toNat - 48 + 16 = (sp - 32).toNat by omega]
  icases stk_split n (sp - 32).toNat 8 24 $$ Hs with ⟨F8, Hs⟩
  icases stk_split n ((sp - 32).toNat + 8) 8 16 $$ Hs with ⟨W8, Hs⟩
  icases stk_split n ((sp - 32).toNat + 8 + 8) 8 8 $$ Hs with ⟨X8, Hs⟩
  icases stk_split n ((sp - 32).toNat + 8 + 8 + 8) 4 4 $$ Hs with ⟨Y4, Z4⟩
  iunfold stk at W8 X8 Y4
  icases W8 with ⟨%w8, %hw8, W8⟩
  icases X8 with ⟨%x8, %hx8, X8⟩
  icases Y4 with ⟨%y4, %hy4, Y4⟩
  icases U128From.memBytes_split n ((sp - 32).toNat + 8) 4 w8 (by omega) $$ W8 with ⟨W0, W4⟩
  simp only [f502]
  rw [show (120 + cost554 m.toNat) * cfg.regularOpCost + R =
    120 * cfg.regularOpCost + (cost554 m.toNat * cfg.regularOpCost + R) by rw [Nat.add_mul]; omega]
  generalize hK : cost554 m.toNat * cfg.regularOpCost = K
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [S8] with (simp [UInt32.toNat_add]; omega)
  mstep [Y4] with (simp [UInt32.toNat_add]; omega)
  ihave S04 := KeyGet.join64 n s.toNat p c $$ [S0 S4]
  · iframe S0 S4
  mstep; mstep
  mstep [S04]
  rw [ofNat_decode_pair]
  mstep [X8] with (simp [UInt32.toNat_add]; omega)
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep; mstep
  ihave X8 := KeyGet.split64 n ((sp - 32).toNat + 8 + 8) p c $$ X8
  icases X8 with ⟨X0, X4⟩
  ihave S04 := KeyGet.split64 n s.toNat p c $$ S04
  icases S04 with ⟨S0, S4⟩
  mcall (f779_s cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (sp - 32 + 8) (sp - 32 + 16) p c m
      (w8.take 4) (w8.drop 4) (by simp; omega) (by simp; omega)) using [X0 X4 Y4 W0 W4]
  · ihave X0 := memBytes_addr (show (sp - 32).toNat + 8 + 8 = (sp - 32 + 16).toNat by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ X0
    ihave X4 := memBytes_addr (show (sp - 32).toNat + 8 + 8 + 4 = (sp - 32 + 16).toNat + 4 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ X4
    ihave Y4 := memBytes_addr (show (sp - 32).toNat + 8 + 8 + 8 = (sp - 32 + 16).toNat + 8 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ Y4
    ihave W0 := memBytes_addr (show (sp - 32).toNat + 8 = (sp - 32 + 8).toNat by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ W0
    ihave W4 := memBytes_addr (show (sp - 32).toNat + 8 + 4 = (sp - 32 + 8).toNat + 4 by
      rw [UInt32.toNat_add, h32]; simp; omega) $$ W4
    iframe X0 X4 Y4 W0 W4
  icases HQ with ⟨%hrs, X0, X4, Y4, W0, W4⟩
  subst hrs
  mcredits (50 * cfg.regularOpCost + (K + R))
  ihave S16 := stk_addr (show sp.toNat - 48 = (sp - 32).toNat - 16 by omega) $$ S16
  mstep; mstep; mstep; mstep [W0] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep [W4] with (simp [UInt32.toNat_add]; omega)
  have hK2 : (13 + cost554 m.toNat) * cfg.regularOpCost = 13 * cfg.regularOpCost + K := by rw [Nat.add_mul, hK]
  mcall (f554_spec cfg lim (d + 1) types[13]! (by rfl) inst mi n g hn hg a673 ha673 (by omega) Cg gt (sp - 32) p m bs
      hbs hp (by omega)) using [Hg S16 Hb]
  · iframe Hg S16 Hb
  icases HQ with ⟨%hrs, Hg, S16, Hb⟩
  subst hrs
  rw [if_pos hv]
  try rw [hK2]
  mcredits (30 * cfg.regularOpCost + R)
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨O4, O12⟩
  mstep; mstep
  ihave X8 := KeyGet.join64 n ((sp - 32 + 16).toNat) p c $$ [X0 X4]
  · iframe X0 X4
  mstep; mstep; mstep [X8] with (simp [UInt32.toNat_add]; omega)
  rw [ofNat_decode_pair]
  mstep [O4]
  rw [storeBytes_pair64]
  mstep; mstep; mstep; mstep; mstep [Y4] with (simp [UInt32.toNat_add]; omega)
  mstep [O12] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep; mstep
  mstep; mstep; mstep [O0]
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  ihave O4 := KeyGet.split64 n (out.toNat + 4) p c $$ O4
  icases O4 with ⟨O4, O8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega, show out.toNat + 4 + 8 = out.toNat + 12 by omega]
  iframe Hg O0 O4 O8 O12 S0 S4 S8 Hb
  ihave W0 := stk_word n _ _ $$ W0
  ihave W4 := stk_word n _ _ $$ W4
  ihave W8 := stk_join n (sp - 32 + 8).toNat 4 4 $$ [W0 W4]
  · iframe W0 W4
  ihave W8 := stk_addr (show (sp - 32 + 8).toNat = (sp - 32).toNat + 8 by rw [UInt32.toNat_add, h32]; simp; omega) $$ W8
  ihave X8 := stk_intro n _ _ $$ X8
  rw [show (bytes32 p ++ bytes32 c).length = 8 by simp]
  ihave X8 := stk_addr (show (sp - 32 + 16).toNat = (sp - 32).toNat + 8 + 8 by rw [UInt32.toNat_add, h32]; simp; omega) $$ X8
  ihave Y4 := stk_word n _ _ $$ Y4
  ihave Y4 := stk_addr (show (sp - 32 + 16).toNat + 8 = (sp - 32).toNat + 8 + 8 + 8 by rw [UInt32.toNat_add, h32]; simp; omega) $$ Y4
  ihave J := stk_join n ((sp - 32).toNat + 8 + 8 + 8) 4 4 $$ [Y4 Z4]
  · iframe Y4 Z4
  ihave J := stk_join n ((sp - 32).toNat + 8 + 8) 8 8 $$ [X8 J]
  · iframe X8 J
  ihave J := stk_join n ((sp - 32).toNat + 8) 8 16 $$ [W8 J]
  · iframe W8 J
  ihave J := stk_join n (sp - 32).toNat 8 24 $$ [F8 J]
  · iframe F8 J
  ihave S16 := stk_addr (show (sp - 32).toNat - 16 = sp.toNat - 48 by omega) $$ S16
  ihave J := stk_addr (show (sp - 32).toNat = sp.toNat - 48 + 16 by omega) $$ J
  iapply stk_join n (sp.toNat - 48) 16 32
  iframe S16 J

end L502v

end WNear.Binary.SerdeAccountId

namespace WNear.Binary.SerdeAccountId

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr
  ofNat_decode_pair storeBytes_pair64)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AccountIdValid (cost554 f554_spec)

section L501

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`TryInto::try_into(out, s)`** (501): 502 on a copy of the `String` in a 16-byte frame. -/
theorem f501_valid (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a673 a554 a779 a502 : Nat)
    (ha673 : mi.funcAddrs[673]? = some a673) (ha554 : mi.funcAddrs[554]? = some a554)
    (ha779 : mi.funcAddrs[779]? = some a779) (ha502 : mi.funcAddrs[502]? = some a502)
    (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out s p c m : UInt32) (ob bs : List UInt8) (hob : ob.length = 16)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hs : s.toNat + 12 ≤ 2 ^ 32) (hbs : bs.length = m.toNat)
    (hp : p.toNat + m.toNat ≤ 2 ^ 32) (hsp : 64 ≤ sp.toNat) (hv : validAccountIdBytes bs = true) :
    a673 ↪[wf] FuncInst.wasm types[31]! inst f673 ∗ a554 ↪[wf] FuncInst.wasm types[13]! inst f554 ∗
      a779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ a502 ↪[wf] FuncInst.wasm types[14]! inst f502 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f501 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 s]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 64) 64 ∗
          n ↦[wms][ out.toNat ] ob ∗ n ↦[i32][ s.toNat ] p ∗ n ↦[i32][ s.toNat + 4 ] c ∗
          n ↦[i32][ s.toNat + 8 ] m ∗ n ↦[wms][ p.toNat ] bs))
        (fun _ => (160 + cost554 m.toNat) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 64) 64 ∗
          n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] c ∗
          n ↦[i32][ out.toNat + 12 ] m ∗ n ↦[i32][ s.toNat ] p ∗ n ↦[i32][ s.toNat + 4 ] c ∗
          n ↦[i32][ s.toNat + 8 ] m ∗ n ↦[wms][ p.toNat ] bs)) := by
  iintro ⟨#F673, #F554, #F779, #F502, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Ho, S0, S4, S8, Hb⟩
  subst hargs
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  icases stk_split n (sp.toNat - 64) 48 16 $$ Hs with ⟨S48, Hs⟩
  rw [show sp.toNat - 64 + 48 = (sp - 16).toNat by omega]
  icases stk_split n (sp - 16).toNat 8 8 $$ Hs with ⟨X8, Hs⟩
  icases stk_split n ((sp - 16).toNat + 8) 4 4 $$ Hs with ⟨Y4, Z4⟩
  iunfold stk at X8 Y4
  icases X8 with ⟨%x8, %hx8, X8⟩
  icases Y4 with ⟨%y4, %hy4, Y4⟩
  simp only [f501]
  rw [show (160 + cost554 m.toNat) * cfg.regularOpCost + R =
    40 * cfg.regularOpCost + ((120 + cost554 m.toNat) * cfg.regularOpCost + R) by simp only [Nat.add_mul]; omega]
  generalize hK : (120 + cost554 m.toNat) * cfg.regularOpCost = K
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [S8] with (simp [UInt32.toNat_add]; omega)
  mstep [Y4] with (simp [UInt32.toNat_add]; omega)
  ihave S04 := KeyGet.join64 n s.toNat p c $$ [S0 S4]
  · iframe S0 S4
  mstep; mstep
  mstep [S04]
  rw [ofNat_decode_pair]
  mstep [X8]
  rw [storeBytes_pair64]
  mstep; mstep
  ihave X8 := KeyGet.split64 n (sp - 16).toNat p c $$ X8
  icases X8 with ⟨X0, X4⟩
  ihave S04 := KeyGet.split64 n s.toNat p c $$ S04
  icases S04 with ⟨S0, S4⟩
  have key := f502_valid (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n g hn hg a673 a554 a779 ha673 ha554
    ha779 (by omega) Cg gt (sp - 16) out (sp - 16) p c m ob bs hob hout (by omega) hbs hp (by omega) hv
  rw [hK] at key
  mcall key using [Hg S48 Ho X0 X4 Y4 Hb]
  · ihave S48 := stk_addr (show sp.toNat - 64 = (sp - 16).toNat - 48 by omega) $$ S48
    ihave Y4 := memBytes_addr (show (sp - 16).toNat + 8 = (sp - 16).toNat + 8 by rfl) $$ Y4
    iframe Hg S48 Ho X0 X4 Y4 Hb
  clear key
  icases HQ with ⟨%hrs, Hg, S48, O0, O4, O8, O12, X0, X4, Y4, Hb⟩
  subst hrs
  mcredits (10 * cfg.regularOpCost + R)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 16 + 16 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hg O0 O4 O8 O12 S0 S4 S8 Hb
  ihave X0 := stk_word n _ _ $$ X0
  ihave X4 := stk_word n _ _ $$ X4
  ihave Y4 := stk_word n _ _ $$ Y4
  ihave J := stk_join n (sp - 16).toNat 4 4 $$ [X0 X4]
  · iframe X0 X4
  ihave J2 := stk_join n ((sp - 16).toNat + 8) 4 4 $$ [Y4 Z4]
  · iframe Y4 Z4
  ihave J := stk_join n (sp - 16).toNat 8 8 $$ [J J2]
  · iframe J J2
  ihave S48 := stk_addr (show (sp - 16).toNat - 48 = sp.toNat - 64 by omega) $$ S48
  ihave J := stk_addr (show (sp - 16).toNat = sp.toNat - 64 + 48 by omega) $$ J
  iapply stk_join n (sp.toNat - 64) 48 16
  iframe S48 J

end L501

end WNear.Binary.SerdeAccountId
