import Bridge.Functions.SerdeStruct
import Bridge.Functions.SerializeStrTab

/-!
# The struct pieces of `SerdeStruct` over any piece of `ESCAPE`

`SerdeStruct.strFn_esc`, `str_out`, `keyFirst_out` and `keyRest_out` with the strings' bytes
landing on zero entries of any piece `et` of `ESCAPE` (`SerializeStr.EscZero lo et`, through
`f344_tab`) instead of an all-zero chunk: `strFn_tab`, `str_out_tab`, `keyFirst_tab`,
`keyRest_tab` (what they read besides the `Compound`: `keyInT`). The same proofs, at the same
costs. A string of letters, digits, spaces and punctuation, or a key with `_`, needs them.
-/

namespace WNear.Binary.SerdeStruct

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)
open WNear.Binary.U128From (memBytes_split memBytes_join)
open WNear.Binary.BorshFT (splitB joinB stkJ stkSp stkA)
open WNear.Binary.FmtSink (roomPre roomPost)
open WNear.Binary.SerializeStr (EscZero serCode escCode cost344 cost383 f344_tab f367_ok)

section Tab

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- `serialize_str` (`strFn ce`, `ce` with 367's code) of `k` bytes landing on zero entries of
`ESCAPE`: as `SerializeStr.f383_tab`. -/
theorem strFn_tab (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat) (ce : Nat) (hce : ce < 955)
    (gt : GlobalType) (s ser vec ptr cap len p k : UInt32) (ob ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hob : ob.length = k.toNat + 2) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8)
    (hdig : EscZero lo et ds) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hvec : vec.toNat + 12 ≤ 2 ^ 32)
    (hroom : len.toNat + k.toNat + 2 ≤ cap.toNat)
    (hptr : ptr.toNat + cap.toNat < 2 ^ 32) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    serCode inst mi A ∗ A ce ↪[wf] FuncInst.wasm types[35]! inst f367
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (strFn ce) Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] len ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ob ∗ n ↦[wms][ p.toNat ] ds))
        (fun _ => cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          n ↦[i32][ ser.toNat ] vec ∗
          n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] (len + k + 2) ∗
          n ↦[wms][ ptr.toNat + len.toNat ] ([34] ++ ds ++ [34]) ∗ n ↦[wms][ p.toNat ] ds)) := by
  iintro ⟨#Hk, #H367⟩
  ihave #S344 := f344_tab (GF := GF) cfg lim (d + 1) types[48]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt s ser ser vec ptr cap len p k ob ds hs hob hds hk0 lo et hdig hser hvec hroom hptr hp $$ Hk
  iunfold serCode at Hk
  icases Hk with ⟨#He, -, #H344, -⟩
  iunfold escCode at He
  icases He with ⟨#Happ, -, -, -, -⟩
  iunfold VecAppend.appCode at Happ
  icases Happ with ⟨-, -, -, -, -, -, #Hi⟩
  have ha344 := hm.funcs 344 (by decide)
  have hace := hm.funcs ce hce
  have t48 : types[48]!.params.length = 4 := by rfl
  have t35 : types[35]!.params.length = 1 := by rfl
  unfold cost383
  rw [Nat.add_mul]
  generalize cost344 k.toNat * cfg.regularOpCost = C
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, HP⟩
  subst hargs
  simp only [strFn]
  repeat mstep
  mcall S344 using [HP]
  · iframe HP
  icases HQ with ⟨%hrs, HP⟩
  subst hrs
  mcall (f367_ok cfg lim (d + 1) types[35]! (by rfl) inst mi Cg) using []
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  repeat mstep
  mstep_post
  mcredits R
  iframe Hc HP
  ipureintro; simp [htype]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **`serialize_str` on `outV`** (`strFn ce`): the JSON string `"ds"` appended, `ds` in a zero
piece of `ESCAPE` (`EscZero lo et`). -/
theorem str_out_tab (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat) (ce : Nat) (hce : ce < 955)
    (gt : GlobalType) (s ser vec ptr cap p k : UInt32) (w ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8)
    (hdig : EscZero lo et ds) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + k.toNat + 2 ≤ cap.toNat)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    serCode inst mi A ∗ A ce ↪[wf] FuncInst.wasm types[35]! inst f367
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (strFn ce) Cg
        (fun args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap w ∗ n ↦[wms][ p.toNat ] ds))
        (fun _ => cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
          n ↦[i32][ ser.toNat ] vec ∗ outV n vec ptr cap (w ++ ([34] ++ ds ++ [34])) ∗ n ↦[wms][ p.toNat ] ds)) := by
  have hl := ofNat_len (w := w) (cap := cap) (by omega)
  refine MFunSpec_wrap (α := List UInt8 × List UInt8)
    (fun x => x.1.length = k.toNat + 2 ∧ w.length + (k.toNat + 2) + x.2.length = cap.toNat ∧
      ptr.toNat + cap.toNat < 2 ^ 32 ∧ vec.toNat + 12 ≤ 2 ^ 32)
    (P0 := fun x args => iprop(⌜args = [.i32 ser, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
      n ↦[i32][ ser.toNat ] vec ∗
      n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat w.length ∗
      n ↦[wms][ ptr.toNat + (UInt32.ofNat w.length).toNat ] x.1 ∗ n ↦[wms][ p.toNat ] ds))
    (Q0 := fun _ _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      stk n (s.toNat - 48) 48 ∗ n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗
      n ↦[i32][ ser.toNat ] vec ∗
      n ↦[i32][ vec.toNat ] ptr ∗ n ↦[i32][ vec.toNat + 4 ] cap ∗
      n ↦[i32][ vec.toNat + 8 ] (UInt32.ofNat w.length + k + 2) ∗
      n ↦[wms][ ptr.toNat + (UInt32.ofNat w.length).toNat ] ([34] ++ ds ++ [34]) ∗ n ↦[wms][ p.toNat ] ds))
    (fun x => iprop(n ↦[wms][ ptr.toNat ] w ∗ n ↦[wms][ ptr.toNat + w.length + (k.toNat + 2) ] x.2))
    (fun x hx => strFn_tab cfg lim d type htype inst mi A n g ta hm hd Cg ce hce gt s ser vec ptr cap
      (UInt32.ofNat w.length) p k x.1 ds hs hx.1 hds hk0 lo et hdig hser hx.2.2.2 (by omega) hx.2.2.1 hp) ?_ ?_
  · intro args
    iintro ⟨%ha, Hg, Hs, Hq, He, Hser, Ho, Hds⟩
    icases outV_open n vec ptr cap w (k.toNat + 2) (by omega) $$ Ho with
      ⟨%ob, %rest, %⟨h1, h2, h3, h4⟩, V0, V4, V8, Hw, Hob, Hr⟩
    iexists (ob, rest)
    isplitr
    · ipureintro; exact ⟨h1, h2, h3, h4⟩
    iframe Hw Hr Hg Hs Hq He Hser V0 V4 V8 Hob Hds
    ipureintro; exact ha
  · intro x hx args rs
    iintro ⟨⟨Hw, Hr⟩, %hrs, Hg, Hs, Hq, He, Hser, V0, V4, V8, Hb, Hds⟩
    iframe Hg Hs Hq He Hser Hds
    isplitr
    · ipureintro; exact hrs
    obtain ⟨h1, h2, h3, h4⟩ := hx
    iapply outV_close n vec ptr cap (UInt32.ofNat w.length + k + 2) w ([34] ++ ds ++ [34]) x.2
      (by simp only [UInt32.toNat_add, hl]; have := cap.toNat_lt; simp; omega) (by simp; omega) h3 h4
    iframe V0 V4 V8 Hw
    isplitl [Hb]
    · iapply memBytes_addr (by rw [hl]) $$ Hb
    iapply memBytes_addr (by simp; omega) $$ Hr

/-- What a key writer (`keyFn cw a ck`) reads besides the `Compound`: the quote, the `ESCAPE`
chunk, `*ser = vec`, the output and the key's bytes. -/
def keyInT (n : Nat) (ser vec ptr cap : UInt32) (w : List UInt8) (lo : Nat) (et : List UInt8) (p : UInt32) (ds : List UInt8) :
    IProp GF :=
  iprop(n ↦[wms][ 1051817 ] [34] ∗ n ↦[wms][ 1061808 + lo ] et ∗ n ↦[i32][ ser.toNat ] vec ∗
    outV n vec ptr cap w ∗ n ↦[wms][ p.toNat ] ds)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The key of a struct's first field** (`keyFn cw a ck` with the state byte 1, `First`): no
comma; the state 2; the key `"ds"` appended (`ck = strFn ce`). -/
theorem keyFirst_tab (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat) (cw ck ce : Nat) (a : UInt32)
    (hck : ck < 955) (hce : ce < 955)
    (gt : GlobalType) (s c ser vec ptr cap p k : UInt32) (w ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hc : c.toNat + 8 ≤ 2 ^ 32) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8)
    (hdig : EscZero lo et ds) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + k.toNat + 2 ≤ cap.toNat)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    serCode inst mi A ∗ A ck ↪[wf] FuncInst.wasm types[15]! inst (strFn ce) ∗
      A ce ↪[wf] FuncInst.wasm types[35]! inst f367
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (keyFn cw a ck) Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [1] ∗
          keyInT n ser vec ptr cap w lo et p ds))
        (fun _ => 30 * cfg.regularOpCost + cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          keyInT n ser vec ptr cap (w ++ ([34] ++ ds ++ [34])) lo et p ds)) := by
  iintro ⟨#Hk, #Hck, #Hce⟩
  ihave #S := str_out_tab (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg ce hce gt s ser
    vec ptr cap p k w ds hs hds hk0 lo et hdig hser hroom hp $$ [Hk Hce]
  · iframe Hk Hce
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold serCode, escCode, VecAppend.appCode at Hk; icases Hk with ⟨⟨⟨-, -, -, -, -, -, #Hi⟩, -⟩, -⟩; iexact Hi
  have hn := hm.mem
  have hack := hm.funcs ck hck
  have t15 : types[15]!.params.length = 3 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, HK⟩
  subst hargs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  simp only [keyFn]
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hcs]
  repeat mstep
  have hloc : actSize ((strFn ce).locals.map ValType.default) = 0 := rfl
  mcall S using [Hg Hs Hq He Hser Ho Hds]
    with (mstep_norm_full; simp only [hloc, Nat.reduceAdd, Nat.reduceDiv] at *; omega)
  · iframe Hg Hs Hq He Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs, Hq, He, Hser, Ho, Hds⟩
  subst hrs
  repeat mstep
  mstep_post
  simp only [hloc, Nat.reduceAdd, Nat.reduceDiv, show storeBytes (Value.i32 2) 1 = ([2] : List UInt8) from rfl]
  mcredits R
  iframe Hc Hg Hs Hcs Hst
  isplitr
  · ipureintro; simp [htype]
  iunfold keyInT
  iframe Hq He Hser Ho Hds

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- **The key of a struct's later field** (`keyFn cw a ck` with the state byte 2, `Rest`): the
comma `cb` at `a` through `cw` (345's code), then the key `"ds"` (`ck = strFn ce`). -/
theorem keyRest_tab (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 9 < lim.maxCallDepth) (Cg : Nat) (cw ck ce : Nat) (a : UInt32)
    (hcw : cw < 955) (hck : ck < 955) (hce : ce < 955) (cb : UInt8)
    (gt : GlobalType) (s c ser vec ptr cap p k : UInt32) (w ds : List UInt8) (hs : 48 ≤ s.toNat)
    (hc : c.toNat + 8 ≤ 2 ^ 32) (hds : ds.length = k.toNat) (hk0 : 0 < k.toNat) (lo : Nat) (et : List UInt8)
    (hdig : EscZero lo et ds) (hser : ser.toNat + 4 ≤ 2 ^ 32) (hroom : w.length + 1 + k.toNat + 2 ≤ cap.toNat)
    (hp : p.toNat + k.toNat ≤ 2 ^ 32) (ha : a.toNat + 1 ≤ 2 ^ 32) :
    serCode inst mi A ∗ A cw ↪[wf] FuncInst.wasm types[31]! inst f345 ∗
      A ck ↪[wf] FuncInst.wasm types[15]! inst (strFn ce) ∗ A ce ↪[wf] FuncInst.wasm types[35]! inst f367
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi (keyFn cw a ck) Cg
        (fun args => iprop(⌜args = [.i32 c, .i32 p, .i32 k]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ a.toNat ] [cb] ∗ keyInT n ser vec ptr cap w lo et p ds))
        (fun _ => 200 * cfg.regularOpCost + MemCpy.cost 1 * cfg.regularOpCost + cost383 k.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
          stk n (s.toNat - 48) 48 ∗ n ↦[i32][ c.toNat ] ser ∗ n ↦[wms][ c.toNat + 4 ] [2] ∗
          n ↦[wms][ a.toNat ] [cb] ∗ keyInT n ser vec ptr cap (w ++ [cb] ++ ([34] ++ ds ++ [34])) lo et p ds)) := by
  iintro ⟨#Hk, #Hcw, #Hck, #Hce⟩
  ihave #S := str_out_tab (GF := GF) cfg lim (d + 1) types[15]! rfl inst mi A n g ta hm (by omega) Cg ce hce gt s ser
    vec ptr cap p k (w ++ [cb]) ds hs hds hk0 lo et hdig hser (by simp; omega) hp $$ [Hk Hce]
  · iframe Hk Hce
  ihave #Happ : VecAppend.appCode inst mi A $$ []
  · iunfold serCode, escCode at Hk; icases Hk with ⟨⟨#H, -⟩, -⟩; iexact H
  ihave #SW := wa_out (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s ser vec
    ptr cap a 1 w [cb] (by omega) rfl hser (by simp; omega) (by simpa using ha) $$ Happ
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold VecAppend.appCode at Happ; icases Happ with ⟨-, -, -, -, -, -, #Hi⟩; iexact Hi
  have hn := hm.mem
  have hack := hm.funcs ck hck
  have hacw := hm.funcs cw hcw
  have t15 : types[15]!.params.length = 3 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  generalize cost383 k.toNat * cfg.regularOpCost = C
  generalize hM : MemCpy.cost (UInt32.toNat 1) * cfg.regularOpCost = M
  rw [show MemCpy.cost 1 * cfg.regularOpCost = M by rw [← hM]; rfl]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hcs, Hst, Hcb, HK⟩
  subst hargs
  iunfold keyInT at HK
  icases HK with ⟨Hq, He, Hser, Ho, Hds⟩
  icases stk_split n (s.toNat - 48) 32 16 $$ Hs with ⟨Hs32, Hs16⟩
  ihave Hs16 := stk_addr (show s.toNat - 48 + 32 = s.toNat - 16 by omega) $$ Hs16
  simp only [keyFn]
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hcs]
  repeat mstep
  mcall SW using [Hg Hs16 Hser Ho Hcb]
  · iframe Hg Hs16 Hser Ho Hcb
  icases HQ with ⟨%hrs, Hg, Hs16, Hser, Ho, Hcb⟩
  subst hrs
  repeat mstep
  mstep [Hst]
  repeat mstep
  mstep [Hcs]
  repeat mstep
  ihave Hs16 := stk_addr (show s.toNat - 16 = s.toNat - 48 + 32 by omega) $$ Hs16
  ihave Hs := stk_join n (s.toNat - 48) 32 16 $$ [Hs32 Hs16]
  · iframe Hs32 Hs16
  have hloc : actSize ((strFn ce).locals.map ValType.default) = 0 := rfl
  mcall S using [Hg Hs Hq He Hser Ho Hds]
    with (mstep_norm_full; simp only [hloc, Nat.reduceAdd, Nat.reduceDiv] at *; omega)
  · iframe Hg Hs Hq He Hser Ho Hds
  icases HQ with ⟨%hrs, Hg, Hs, Hq, He, Hser, Ho, Hds⟩
  subst hrs
  repeat mstep
  mstep_post
  simp only [hloc, Nat.reduceAdd, Nat.reduceDiv, show storeBytes (Value.i32 2) 1 = ([2] : List UInt8) from rfl]
  mcredits R
  iframe Hc Hg Hs Hcs Hst Hcb
  isplitr
  · ipureintro; simp [htype]
  iunfold keyInT
  iframe Hq He Hser Ho Hds


end Tab

end WNear.Binary.SerdeStruct
