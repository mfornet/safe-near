import Bridge.Functions.SerdeStruct78
import Bridge.Functions.DropVec
import Bridge.Functions.JsonSuffix

/-!
# `from_trait` (66) for `ft_balance_of`'s arguments: the accepting run (M6)

```wat
;; 66 from_trait(out, rd)          frame sp' = sp - 64
copy the SliceRead at rd to sp'+48
Deserializer::new(sp', sp'+48)    ;; 634: de = sp': read, scratch (1, 0, 0), depth 128
Input::deserialize(sp'+48, sp')   ;; 78 → 228
Ok(v) → v to sp'+32; end(sp')     ;; 320: only whitespace left
        0 → out := (0, v)
drop the scratch (68 at sp'+12)    ;; capacity 0: nothing to free
```

`f66_acc`: wherever serde's machine `SerdeStructModel.fromSlice` accepts the input with the account
`a`, 66 returns `Ok(a)` at `out`. The callees not proved yet are the hypotheses of `f78_acc`
(`Hyp646`, `Hyp169`, `Hyp81`) and its pure facts. The scratch is never grown on this path (keys
without escapes, `Hyp646`; values that push no frame, `Hyp81`), so its drop (68) frees nothing:
`f747_zero`, `f68_zero` are the drops at capacity 0.
-/

namespace WNear.Binary.SerdeFromTrait

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocTwo (code310)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_intro stk_word stk_addr)
open WNear.Binary.SerdeRead (rd optByte wsLen)
open WNear.Binary.SerdeErrBox (errCode costErr heapA roomFor4)
open WNear.Binary.SerdeEnds (endCode)
open WNear.Binary.SerdeStructArr (strRes tbl Hyp169 roomS stk_join')
open WNear.Binary.SerdeStructObj (Hyp646 Hyp81)
open WNear.Binary.ArgsLeaves (sliceRead deserializer)
open NearInterface.Json

section Drop

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `<RawVec as Drop>::drop` (747) of a `Vec` of capacity 0: nothing to free. -/
theorem f747_zero (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (v : UInt32) (hv : v.toNat + 8 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f747 Cg
        (fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat + 4 ] 0))
        (fun _ => 10 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat + 4 ] 0)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, V4⟩
  subst hargs
  simp only [f747]
  mstep; mstep; mstep [V4]; mstep; mstep
  mstep_taken with decide
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe V4

/-- **`drop_in_place::<Vec<u8>>`** (68) of a `Vec` of capacity 0: nothing to free. -/
theorem f68_zero (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (v : UInt32)
    (hv : v.toNat + 8 ≤ 2 ^ 32) :
    inst ↪[inst] mi ∗ A 747 ↪[wf] FuncInst.wasm types[0]! inst f747 ∗
      A 778 ↪[wf] FuncInst.wasm types[0]! inst f778 ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f68 Cg
        (fun args => iprop(⌜args = [.i32 v]⌝ ∗ n ↦[i32][ v.toNat + 4 ] 0))
        (fun _ => 40 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ v.toNat + 4 ] 0)) := by
  iintro ⟨#Hi, #H747, #H778⟩
  have ha747 := hm.funcs 747 (by decide)
  have ha778 := hm.funcs 778 (by decide)
  have t0 : types[0]!.params.length = 1 := by rfl
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, V4⟩
  subst hargs
  simp only [f68]
  mstep
  mcall (DropVec.f778_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi Cg v) using []
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep
  mcall (f747_zero (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi n hm.mem Cg v hv) using [V4]
  · iframe V4
  icases HQ with ⟨%hrs, V4⟩
  subst hrs
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe V4
  ipureintro; simp [htype]

end Drop


/-- The whitespace left after the struct, when it is all whitespace. -/
theorem wsLen_all {r : List UInt8} (h : skipWhitespace r = []) : wsLen r = r.length := by
  have h1 := SerdeRead.skipWhitespace_eq r
  rw [h] at h1
  have h2 := congrArg List.length h1
  simp at h2
  have := SerdeRead.wsLen_le r
  omega

theorem i64_one : storeBytes (.i64 1) 8 = bytes32 1 ++ bytes32 0 := by decide

section L66

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code 66 runs on its accepting path (persistent). -/
def code66 (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(SerdeNextKey.code193 n maxP inst mi A ∗ A 205 ↪[wf] FuncInst.wasm types[14]! inst f205 ∗
    A 201 ↪[wf] FuncInst.wasm types[32]! inst f201 ∗ A 193 ↪[wf] FuncInst.wasm types[11]! inst f193 ∗
    A 89 ↪[wf] FuncInst.wasm types[32]! inst f89 ∗ A 90 ↪[wf] FuncInst.wasm types[32]! inst f90 ∗
    A 81 ↪[wf] FuncInst.wasm types[32]! inst f81 ∗ A 169 ↪[wf] FuncInst.wasm types[14]! inst f169 ∗
    A 77 ↪[wf] FuncInst.wasm types[0]! inst f77 ∗ A 214 ↪[wf] FuncInst.wasm types[14]! inst f214 ∗
    A 91 ↪[wf] FuncInst.wasm types[32]! inst f91 ∗ A 228 ↪[wf] FuncInst.wasm types[36]! inst f228 ∗
    A 78 ↪[wf] FuncInst.wasm types[14]! inst f78 ∗ A 634 ↪[wf] FuncInst.wasm types[14]! inst f634 ∗
    A 320 ↪[wf] FuncInst.wasm types[32]! inst f320 ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
    A 747 ↪[wf] FuncInst.wasm types[0]! inst f747 ∗ A 778 ↪[wf] FuncInst.wasm types[0]! inst f778)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code66 (GF := GF) n maxP inst mi A) := by
  unfold code66; infer_instance

theorem stk_join'' (n a b k1 k2 : Nat) (h : b = a + k1) :
    stk (GF := GF) n a k1 ∗ stk n b k2 ⊢ stk n a (k1 + k2) := by
  subst h; exact stk_join n a k1 k2

/-- 66's 64-byte frame, from the pieces its accepting path leaves. -/
theorem frame66 (n s : Nat) :
    stk (GF := GF) n s 4 ∗ stk n (s + 4) 4 ∗ stk n (s + 8) 4 ∗ stk n (s + 12) 4 ∗ stk n (s + 16) 4 ∗
      stk n (s + 20) 4 ∗ stk n (s + 24) 1 ∗ stk n (s + 25) 7 ∗ stk n (s + 32) 8 ∗ stk n (s + 40) 4 ∗
      stk n (s + 44) 4 ∗ stk n (s + 48) 4 ∗ stk n (s + 52) 4 ∗ stk n (s + 56) 4 ∗ stk n (s + 60) 4 ⊢
      stk n s 64 := by
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13, H14, H15⟩
  ihave H14 := stk_join'' n (s + 56) (s + 60) 4 4 (by omega) $$ [H14 H15]
  · iframe H14 H15
  ihave H13 := stk_join'' n (s + 52) (s + 56) 4 8 (by omega) $$ [H13 H14]
  · iframe H13 H14
  ihave H12 := stk_join'' n (s + 48) (s + 52) 4 12 (by omega) $$ [H12 H13]
  · iframe H12 H13
  ihave H11 := stk_join'' n (s + 44) (s + 48) 4 16 (by omega) $$ [H11 H12]
  · iframe H11 H12
  ihave H10 := stk_join'' n (s + 40) (s + 44) 4 20 (by omega) $$ [H10 H11]
  · iframe H10 H11
  ihave H9 := stk_join'' n (s + 32) (s + 40) 8 24 (by omega) $$ [H9 H10]
  · iframe H9 H10
  ihave H8 := stk_join'' n (s + 25) (s + 32) 7 32 (by omega) $$ [H8 H9]
  · iframe H8 H9
  ihave H7 := stk_join'' n (s + 24) (s + 25) 1 39 (by omega) $$ [H7 H8]
  · iframe H7 H8
  ihave H6 := stk_join'' n (s + 20) (s + 24) 4 40 (by omega) $$ [H6 H7]
  · iframe H6 H7
  ihave H5 := stk_join'' n (s + 16) (s + 20) 4 44 (by omega) $$ [H5 H6]
  · iframe H5 H6
  ihave H4 := stk_join'' n (s + 12) (s + 16) 4 48 (by omega) $$ [H4 H5]
  · iframe H4 H5
  ihave H3 := stk_join'' n (s + 8) (s + 12) 4 52 (by omega) $$ [H3 H4]
  · iframe H3 H4
  ihave H2 := stk_join'' n (s + 4) (s + 8) 4 56 (by omega) $$ [H2 H3]
  · iframe H2 H3
  iapply stk_join'' n s (s + 4) 4 60 (by omega)
  iframe H1 H2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- **`from_trait` (66) on an accepted input**: wherever serde's machine reads the struct `a` and
then only whitespace (`structDe … = some (a, r)`, `skipWhitespace r = []`), `out` gets `Ok(a)`.
The hypotheses on the callees are `f78_acc`'s, at the `Deserializer` in 66's frame (`sp - 64`). -/
theorem f66_acc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 23 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hrd : rd.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hsp : 400 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hr : roomS mlen maxP)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (K646 K169 K81 : Nat → Nat) (Fb : Nat) (Cd : IProp GF) [Persistent Cd]
    (h646 : Hyp646 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP K646 Cd)
    (h169 : Hyp169 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP dv K169 Fb Cd)
    (h81 : Hyp81 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP ign K81 Cd) (hF : F ≤ Fb)
    (hdv0 : dv [] = none)
    (hdvs : ∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r)
    (higns : ∀ j r, j ≤ bs.length → ign (bs.drop j) = some ((), r) → bs.drop (bs.length - r.length) = r)
    (hstrs : ∀ q k r, q ≤ bs.length → stringBody (bs.drop q) [] = some (some k, r) → bs.drop (bs.length - r.length) = r)
    (a : WNear.AccountId) (r : List UInt8)
    (hS : SerdeStructModel.structDe "account_id" dv ign bs = some (a, r)) (hE : skipWhitespace r = [])
    (hsuf : bs.drop (bs.length - r.length) = r) :
    code66 n maxP inst mi A ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 400) 400 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗
          sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => (425 + 96 * r.length) * cfg.regularOpCost + SerdeStruct78.costS cfg K646 K169 K81 dv ign bs)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 400) 400 ∗
          vt n 1057464 idx ta (A 578) ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗
          n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap)) := by
  iintro ⟨#Hc66, #HCd⟩
  ihave #Hc66' := Hc66
  iunfold code66 at Hc66'
  icases Hc66' with ⟨#H193c, #F205, #F201, #F193, #F89, #F90, #F81, #F169, #F77, #F214, #F91, #F228,
    #F78, #F634, #F320, #F68, #F747, #F778⟩
  ihave #Hv := H193c
  iunfold SerdeNextKey.code193 at Hv
  icases Hv with ⟨#Hv, -, -, -, -, -, -, -⟩
  ihave #Hv' := Hv
  iunfold SerdeEnds.endCode at Hv'
  icases Hv' with ⟨#Hcode, -⟩
  iunfold SerdeErrBox.errCode at Hcode
  icases Hcode with ⟨#H310c, -⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold AllocTwo.code310 at H310c
    icases H310c with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hi⟩
    iexact Hi
  have hn := hm.mem
  have hg := hm.glob
  have ha634 := hm.funcs 634 (by decide)
  have ha78 := hm.funcs 78 (by decide)
  have ha320 := hm.funcs 320 (by decide)
  have ha68 := hm.funcs 68 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h48 : (sp - 64 + 48).toNat = (sp - 64).toNat + 48 := by simp [UInt32.toNat_add]; omega
  have h12 : (sp - 64 + 12).toNat = (sp - 64).toNat + 12 := by simp [UInt32.toNat_add]; omega
  -- the struct's rest, and `end`'s side
  have hrl : r.length ≤ bs.length := by
    have := congrArg List.length hsuf; simp at this; omega
  have hwr : wsLen (bs.drop (bs.length - r.length)) = r.length := by rw [hsuf]; exact wsLen_all hE
  have hok : bs.length - r.length + wsLen (bs.drop (bs.length - r.length)) = bs.length := by omega
  generalize hCS : SerdeStruct78.costS cfg K646 K169 K81 dv ign bs = CS
  rw [Nat.add_mul]
  generalize hW : 96 * r.length * cfg.regularOpCost = W
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hvt, Hh, Ho, Hsr, Hbs, He, Hw, Hkey, Hid⟩
  subst hargs
  -- the frame
  icases stk_split n (sp.toNat - 400) 336 64 $$ Hs with ⟨S336, F64⟩
  rw [show sp.toNat - 400 + 336 = (sp - 64).toNat by omega, show sp.toNat - 400 = (sp - 64).toNat - 336 by omega]
  icases stk_split n (sp - 64).toNat 8 56 $$ F64 with ⟨O0, F56⟩
  icases stk_split n ((sp - 64).toNat + 8) 4 52 $$ F56 with ⟨O8, F52⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4) 8 44 $$ F52 with ⟨O12, F44⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8) 4 40 $$ F44 with ⟨O20, F40⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4) 1 39 $$ F40 with ⟨O24, F39⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1) 7 32 $$ F39 with ⟨X25, F32⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7) 8 24 $$ F32 with ⟨A32, F24⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8) 4 20 $$ F24 with ⟨A40, F20⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4) 4 16 $$ F20 with ⟨A44, F16⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4) 8 8 $$ F16 with ⟨B48, F8⟩
  icases stk_split n ((sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8) 4 4 $$ F8 with ⟨B56, B60⟩
  rw [show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8 + 4 = (sp - 64).toNat + 60 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 + 8 = (sp - 64).toNat + 56 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 + 4 = (sp - 64).toNat + 48 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 + 4 = (sp - 64).toNat + 44 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 + 8 = (sp - 64).toNat + 40 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 + 7 = (sp - 64).toNat + 32 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 + 1 = (sp - 64).toNat + 25 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 + 4 = (sp - 64).toNat + 24 by omega,
    show (sp - 64).toNat + 8 + 4 + 8 = (sp - 64).toNat + 20 by omega,
    show (sp - 64).toNat + 8 + 4 = (sp - 64).toNat + 12 by omega]
  iunfold stk at O0 O8 O12 O20 O24 B48 B56
  icases O0 with ⟨%o0, %ho0, O0⟩
  icases O8 with ⟨%o8, %ho8, O8⟩
  icases O12 with ⟨%o12, %ho12, O12⟩
  icases O20 with ⟨%o20, %ho20, O20⟩
  icases O24 with ⟨%o24, %ho24, O24⟩
  icases B48 with ⟨%b48, %hb48, B48⟩
  icases B56 with ⟨%b56, %hb56, B56⟩
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨Q0, Ho⟩
  icases U128From.memBytes_split n (out.toNat + 4) 8 (ob.drop 4) (by simp; omega) $$ Ho with ⟨Q4, Q12⟩
  rw [show out.toNat + 4 + 8 = out.toNat + 12 by omega]
  iunfold sliceRead at Hsr
  icases Hsr with ⟨R0, R4, R8⟩
  ihave R := KeyGet.join64 n rd.toNat ptr (UInt32.ofNat bs.length) $$ [R0 R4]
  · iframe R0 R4
  simp only [f66]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [R8]
  mstep [B56]
  mstep; mstep
  mstep [R]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [B48]
  rw [VecFromElem.storeBytes_pair64]
  ihave B48 := KeyGet.split64 n ((sp - 64).toNat + 48) ptr (UInt32.ofNat bs.length) $$ B48
  icases B48 with ⟨B48, B52⟩
  have s634 := ArgsLeaves.f634_spec (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (sp - 64)
    (sp - 64 + 48) ptr (UInt32.ofNat bs.length) 0 o0 o8 o12 o20 o24 ho0 ho8 ho12 ho20 ho24 (by omega) (by omega)
  mstep; mstep; mstep; mstep
  mcall s634 using [B48 B52 B56 O0 O8 O12 O20 O24]
  · iunfold sliceRead
    rw [h48]
    iframe B48 B52 B56 O0 O8 O12 O20 O24
  icases HQ with ⟨%hrs, Hsl, HD⟩
  subst hrs
  clear s634
  iunfold sliceRead at Hsl
  rw [h48]
  icases Hsl with ⟨B48, B52, B56⟩
  ihave B48 := stk_word $$ B48
  ihave B52 := stk_word $$ B52
  ihave B56 := stk_word $$ B56
  ihave OB := stk_join n _ 4 4 $$ [B48 B52]
  · iframe B48 B52
  ihave OB := stk_join n _ 8 4 $$ [OB B56]
  · iframe OB B56
  ihave OB := stk_join n _ 12 4 $$ [OB B60]
  · iframe OB B60
  iunfold stk at OB
  icases OB with ⟨%ob2, %hob2, OB⟩
  iunfold deserializer at HD
  icases HD with ⟨Dsr, D12, D20, D24⟩
  ihave Hrd : SerdeRead.rd n (sp - 64) ptr bs 0 $$ [Dsr Hbs]
  · iunfold SerdeRead.rd
    iframe Hbs
    iexact Dsr
  rw [i64_one]
  ihave D12 := KeyGet.split64 n ((sp - 64).toNat + 12) 1 0 $$ D12
  icases D12 with ⟨D12, D16⟩
  rw [show (sp - 64).toNat + 12 + 4 = (sp - 64).toNat + 16 by omega]
  ihave Ht : tbl n (sp - 64) $$ [D20 He Hw D12 D16 Hid]
  · iunfold tbl
    iframe He Hw D12 D16 Hid
    iexists 0
    iexact D20
  have s78 := SerdeStruct78.f78_acc (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi A n g ta hm (by omega) Cg
    gt (sp - 64) (sp - 64 + 48) (sp - 64) ptr idx ob2 bs maxP mlen F live hob2 (by omega) hlen hptr (by omega)
    (by omega) (by omega) hr dv ign K646 K169 K81 Fb Cd h646 h169 h81 hF hdv0 hdvs higns hstrs a r hS
  rw [h48, hCS] at s78
  ihave #S78 := s78 $$ [H193c F205 F201 F193 F89 F90 F81 F169 F77 F214 F91 F228 HCd]
  · iframe H193c F205 F201 F193 F89 F90 F81 F169 F77 F214 F91 F228 HCd
  clear s78
  mstep; mstep; mstep; mstep
  mcall S78 using [Hg S336 Hvt Hh OB Hrd D24 Ht Hkey]
  · iframe Hg S336 Hvt Hh OB Hrd D24 Ht Hkey
  icases HQ with ⟨%hrs, Hg, S336, Hvt, D24, Ht, Hkey, %p, %cap, W0, W4, W8, W12, Hstr, Hrd⟩
  subst hrs
  iunfold stk at A32 A40
  icases A32 with ⟨%a32, %ha32, A32⟩
  icases A40 with ⟨%a40, %ha40, A40⟩
  rw [show (sp - 64).toNat + 48 + 12 = (sp - 64).toNat + 60 by omega,
    show (sp - 64).toNat + 48 + 8 = (sp - 64).toNat + 56 by omega,
    show (sp - 64).toNat + 48 + 4 = (sp - 64).toNat + 52 by omega]
  mstep; mstep; mstep; mstep
  mstep; mstep [W0]; mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep
  mstep [W12]
  mstep [A40]
  ihave W52 := KeyGet.join64 n ((sp - 64).toNat + 52) p cap $$ [W4 W8]
  · rw [show (sp - 64).toNat + 52 + 4 = (sp - 64).toNat + 56 by omega]; iframe W4 W8
  mstep; mstep
  mstep [W52]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [A32]
  rw [VecFromElem.storeBytes_pair64]
  iunfold strRes at Hstr
  icases Hstr with ⟨%mlen', %F', %⟨hp', hcap, hr'⟩, Hbytes, Hblk, Hh⟩
  icases stk_split n ((sp - 64).toNat - 336) 240 96 $$ S336 with ⟨S240, S96⟩
  rw [show (sp - 64).toNat - 336 + 240 = (sp - 64).toNat - 96 by omega]
  have s320 := SerdeEnds.f320_spec (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 64) (sp - 64) ptr idx bs (bs.length - r.length) maxP mlen' ((p.toNat, cap.toNat) :: live) F' hlen hptr
    (by omega) (by omega) (by omega) hr'
  rw [SerdeStructObj.costEnd_ok cfg F' 200 _ _ _ hok, hwr, Nat.add_mul, hW] at s320
  ihave #S320 := s320 $$ Hv
  clear s320
  mstep
  mcall S320 using [Hg S96 Hvt Hh Hrd]
  · iframe Hg S96 Hvt Hh Hrd
  icases HQ with ⟨Hg, S96, Hvt, HQ⟩
  ihave HQ := SerdeValueSeed.resEnd_pos (show bs.length - r.length + r.length = bs.length by omega) $$ HQ
  icases HQ with ⟨%hrs, Hh, Hrd⟩
  subst hrs
  mstep; mstep
  mstep_taken with decide
  mstep; mstep; mstep; mstep; mstep
  mstep [A32]
  rw [VecFromElem.ofNat_decode_pair]
  mstep [Q4]
  rw [VecFromElem.storeBytes_pair64]
  mstep; mstep; mstep [Q0]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [A40]
  mstep [Q12]
  iunfold tbl at Ht
  icases Ht with ⟨Hsl, He, Hw, D12, D16, Hid⟩
  rw [show (sp - 64).toNat + 16 = (sp - 64).toNat + 12 + 4 by omega]
  have s68 := f68_zero (GF := GF) cfg lim (d + 1) types[0]! (by rfl) inst mi A n g ta hm (by omega) Cg
    (sp - 64 + 12) (by omega)
  rw [h12] at s68
  ihave #S68 := s68 $$ [Hi F747 F778]
  · iframe Hi F747 F778
  clear s68
  mstep; mstep; mstep
  mcall S68 using [D16]
  · iframe D16
  icases HQ with ⟨%hrs, D16⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 64 + 64 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg Hvt Hkey Hid
  icases Hsl with ⟨%sl, D20⟩
  iframe He Hw
  iunfold SerdeRead.rd at Hrd
  icases Hrd with ⟨Dsr, Hbs⟩
  iframe Hbs
  ihave R := KeyGet.split64 n rd.toNat ptr (UInt32.ofNat bs.length) $$ R
  icases R with ⟨R0, R4⟩
  isplitl [S240 S96 Dsr D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W12]
  · iunfold sliceRead at Dsr
    icases Dsr with ⟨G0, G4, G8⟩
    ihave S336 := stk_join n ((sp - 64).toNat - 336) 240 96 $$ [S240 S96]
    · rw [show (sp - 64).toNat - 336 + 240 = (sp - 64).toNat - 96 by omega]; iframe S240 S96
    ihave W52 := KeyGet.split64 n ((sp - 64).toNat + 52) p cap $$ W52
    icases W52 with ⟨W52, W56⟩
    ihave G0 := stk_word $$ G0
    ihave G4 := stk_word $$ G4
    ihave G8 := stk_word $$ G8
    ihave D12 := stk_word $$ D12
    ihave D16 := stk_word $$ D16
    ihave D20 := stk_word $$ D20
    ihave D24 := stk_intro $$ D24
    ihave A32 := stk_intro $$ A32
    ihave A40 := stk_word $$ A40
    ihave W0 := stk_word $$ W0
    ihave W52 := stk_word $$ W52
    ihave W56 := stk_word $$ W56
    ihave W12 := stk_word $$ W12
    rw [show (bytes32 p ++ bytes32 cap).length = 8 by simp, show ([128] : List UInt8).length = 1 by rfl,
      show (sp - 64).toNat + 12 + 4 = (sp - 64).toNat + 16 by omega,
      show (sp - 64).toNat + 52 + 4 = (sp - 64).toNat + 56 by omega]
    ihave F64 := frame66 n (sp - 64).toNat $$ [G0 G4 G8 D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W56 W12]
    · iframe G0 G4 G8 D12 D16 D20 D24 X25 A32 A40 A44 W0 W52 W56 W12
    ihave F64 := stk_addr (show (sp - 64).toNat = (sp - 64).toNat - 336 + 336 by omega) $$ F64
    iapply stk_join n ((sp - 64).toNat - 336) 336 64
    iframe S336 F64
  isplitl [R0 R4 R8]
  · iunfold sliceRead
    iframe R0 R4 R8
  iexists p
  iexists cap
  ihave Q4 := KeyGet.split64 n (out.toNat + 4) p cap $$ Q4
  icases Q4 with ⟨Q4, Q8⟩
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  iframe Q0 Q4 Q8 Q12
  iunfold strRes
  iexists mlen'
  iexists F'
  iframe Hbytes Hblk Hh
  ipureintro; exact ⟨hp', hcap, hr'⟩


end L66

/-- The length of the rest after the struct, as serde's machine reads it. -/
def restLen (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (bs : List UInt8) : Nat :=
  match SerdeStructModel.structDe "account_id" dv ign bs with
  | some (_, r) => r.length
  | none => 0

/-- 66's cost on an accepted input: its own, `end`'s whitespace, and the struct's (`costS`). -/
def cost66 (cfg : WasmConfig) (K646 K169 K81 : Nat → Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (bs : List UInt8) : Nat :=
  (425 + 96 * restLen dv ign bs) * cfg.regularOpCost + SerdeStruct78.costS cfg K646 K169 K81 dv ign bs

/-- The model's acceptance, read by serde's machine: `Call.decode` gives `ftBalanceOf a` exactly when
the machine reads the struct `a` and then only whitespace, for any readers that agree with the
model. -/
theorem decode_struct {dv : List UInt8 → Option (WNear.AccountId × List UInt8)}
    {ign : List UInt8 → Option (Unit × List UInt8)} (hdv : SerdeStructModel.Agrees dv (SerdeStructModel.valueAs WNear.account))
    (hign : SerdeStructModel.Agrees ign SerdeStructModel.valueSkip) {bs : List UInt8} {a : WNear.AccountId}
    (h : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)) :
    ∃ r, SerdeStructModel.structDe "account_id" dv ign bs = some (a, r) ∧ skipWhitespace r = [] := by
  rw [SerdeStructModel.decode_balanceOf dv ign hdv hign bs] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨a', h1, h2⟩ := h
  cases h2
  unfold SerdeStructModel.fromSlice at h1
  simp only [Option.bind_eq_some_iff] at h1
  obtain ⟨⟨a2, r⟩, hS, hE⟩ := h1
  unfold SerdeStructModel.endOk at hE
  split at hE
  · simp only [Option.some.injEq] at hE
    subst hE
    exact ⟨r, hS, by assumption⟩
  · simp at hE

/-- The pure facts `f78_acc` needs, from readers that agree with the model. -/
theorem reader_facts {dv : List UInt8 → Option (WNear.AccountId × List UInt8)}
    {ign : List UInt8 → Option (Unit × List UInt8)} (hdv : SerdeStructModel.Agrees dv (SerdeStructModel.valueAs WNear.account))
    (hign : SerdeStructModel.Agrees ign SerdeStructModel.valueSkip) (bs : List UInt8) :
    dv [] = none ∧
    (∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r) ∧
    (∀ j r, j ≤ bs.length → ign (bs.drop j) = some ((), r) → bs.drop (bs.length - r.length) = r) ∧
    (∀ q k r, q ≤ bs.length → stringBody (bs.drop q) [] = some (some k, r) → bs.drop (bs.length - r.length) = r) ∧
    (∀ bs a r, dv bs = some (a, r) → r <:+ bs) ∧ (∀ bs r, ign bs = some ((), r) → r <:+ bs) := by
  have hdvS : ∀ bs a r, dv bs = some (a, r) → r <:+ bs :=
    JsonSuffix.agrees_suf hdv (fun _ _ _ h => JsonSuffix.valueAs_suf _ h)
  have hignS : ∀ bs r, ign bs = some ((), r) → r <:+ bs := fun bs r h =>
    JsonSuffix.agrees_suf hign (fun _ x _ h => by cases x; exact JsonSuffix.valueSkip_suf h) bs () r h
  refine ⟨JsonSuffix.agrees_nil hdv (JsonSuffix.valueAs_nil _), ?_, ?_, ?_, hdvS, hignS⟩
  · intro j a r _ h; exact JsonSuffix.drop_suf' (hdvS _ _ _ h)
  · intro j r _ h; exact JsonSuffix.drop_suf' (hignS _ _ h)
  · intro q k r _ h; exact JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' h)

section L66m

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`from_trait` (66) against the model**: wherever `Call.decode` reads `ftBalanceOf a`, `out`
gets `Ok(a)`, at `cost66`, for any readers `dv` (169) and `ign` (81) that agree with the model and
satisfy the hypotheses `Hyp646`, `Hyp169`, `Hyp81` at 66's `Deserializer` (`sp - 64`). -/
theorem f66_dec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 23 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp out rd ptr idx : UInt32) (ob bs : List UInt8)
    (maxP mlen F : Nat) (live : List (Nat × Nat)) (hob : ob.length = 16) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hrd : rd.toNat + 12 ≤ 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hsp : 400 ≤ sp.toNat) (hal : sp.toNat % 8 = 0) (hr : roomS mlen maxP)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (hdv : SerdeStructModel.Agrees dv (SerdeStructModel.valueAs WNear.account))
    (hign : SerdeStructModel.Agrees ign SerdeStructModel.valueSkip)
    (K646 K169 K81 : Nat → Nat) (Fb : Nat) (Cd : IProp GF) [Persistent Cd]
    (h646 : Hyp646 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP K646 Cd)
    (h169 : Hyp169 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP dv K169 Fb Cd)
    (h81 : Hyp81 cfg lim inst mi n g ta A Cg gt (sp - 64) ptr idx bs maxP ign K81 Cd) (hF : F ≤ Fb)
    (a : WNear.AccountId) (h : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)) :
    code66 n maxP inst mi A ∗ Cd ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f66 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 400) 400 ∗ vt n 1057464 idx ta (A 578) ∗
          heapInv n maxP mlen live F ∗ n ↦[wms][ out.toNat ] ob ∗
          sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗ n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes))
        (fun _ => cost66 cfg K646 K169 K81 dv ign bs)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 400) 400 ∗
          vt n 1057464 idx ta (A 578) ∗ sliceRead n rd ptr (UInt32.ofNat bs.length) 0 ∗
          n ↦[wms][ ptr.toNat ] bs ∗
          n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
          ∃ (p cap : UInt32), n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗
            n ↦[i32][ out.toNat + 8 ] cap ∗ n ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
            strRes n maxP live a p cap)) := by
  obtain ⟨r, hS, hE⟩ := decode_struct hdv hign h
  obtain ⟨hdv0, hdvs, higns, hstrs, hdvS, hignS⟩ := reader_facts hdv hign bs
  have hsuf := JsonSuffix.drop_suf (JsonSuffix.structDe_suf "account_id" dv ign hdvS hignS hS)
  have hrest : restLen dv ign bs = r.length := by unfold restLen; rw [hS]
  unfold cost66
  rw [hrest]
  exact f66_acc cfg lim d type htype inst mi A n g ta hm hd Cg gt sp out rd ptr idx ob bs maxP mlen F live hob hout
    hrd hlen hptr hsp hal hr dv ign K646 K169 K81 Fb Cd h646 h169 h81 hF hdv0 hdvs higns hstrs a r hS hE hsuf

end L66m

end WNear.Binary.SerdeFromTrait
