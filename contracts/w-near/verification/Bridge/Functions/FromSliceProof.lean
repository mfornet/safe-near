import Bridge.Functions.FromSliceSpec
import Bridge.Functions.SerdeKeyNoEsc

/-!
# `ft_balance_of`'s argument parser: the accepting contract, and both halves at 65 (M6)

* `acceptContract`: `FromSliceSpec.AcceptContract 400 K0 K1 X` for every `K0`, `K1`, `X`. Its premise
  `AcceptCallees` carries the callees not proved yet and the cost bound; the proof is
  `SerdeFromTrait.f66_dec` on `wInst`, with the code from the store (`code66_of`).
* `f65_accept`, `f65_reject`: `serde_json::from_slice` (65) from either half of 66's contract, with
  16 more bytes of stack (its `SliceRead`) and 45 more `regular_op_cost`s.
-/

namespace WNear.Binary.FromSliceSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.ArgsLeaves (sliceRead f65_of_66)
open WNear.Binary.InitialState (funcCells)
open WNear.Binary.SerdeErrBox (roomFor4)
open WNear.Binary.SerdeStructArr (strRes)
open WNear.Binary.SerdeFromTrait (code66 cost66 f66_dec)

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The accepting contract of 66 holds**, with a stack of 400 bytes, for any callees that satisfy
`AcceptCallees` (whose cost bound fixes `K0`, `K1`, `X`). -/
theorem acceptContract (K0 K1 X : Nat) : AcceptContract (GF := GF) 400 K0 K1 X := by
  intro cfg h0 lim d hd Cg gt sp out rd ptr idx bs ob hl F live a hS hal hptr hlen hout hob hrd hr hdec hcal
  obtain ⟨dv, ign, K646, K169, K81, hdv, hign, h646, h169, h81, hK⟩ := hcal
  have s := f66_dec (GF := GF) cfg.wasm lim d types[14]! (by rfl) 0 wInst id 0 0 0 Interface.wInst_ifaceMod
    (by omega) Cg gt sp out rd ptr idx ob bs 2048 hl F live hob hout hrd hlen hptr hS (by omega) hr dv ign hdv hign
    K646 K169 K81 F (codeCtx cfg h0) h646 h169 h81 (Nat.le_refl F) a hdec
  simp only [id] at s
  iintro #Hctx
  ihave #C66 := code66_of cfg h0 $$ Hctx
  ihave #S := s $$ [C66 Hctx]
  · iframe C66 Hctx
  clear s
  iapply (AllocGen.MFunSpec_cost (K := fun _ => cost66 cfg.wasm K646 K169 K81 dv ign bs) (fun _ => hK))
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 400) 400 ∗
      vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F ∗ 0 ↦[wms][ out.toNat ] ob ∗
      sliceRead 0 rd ptr (UInt32.ofNat bs.length) 0 ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 400) 400 ∗
      vt 0 1057464 idx 0 578 ∗ sliceRead 0 rd ptr (UInt32.ofNat bs.length) 0 ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗
      ∃ (p cap : UInt32), 0 ↦[i32][ out.toNat ] 0 ∗ 0 ↦[i32][ out.toNat + 4 ] p ∗
        0 ↦[i32][ out.toNat + 8 ] cap ∗ 0 ↦[i32][ out.toNat + 12 ] (UInt32.ofNat a.val.utf8ByteSize) ∗
        strRes 0 2048 live a p cap)) ?hP ?hQ)
  case hP =>
    intro args
    iintro HP
    iunfold pre66 at HP
    icases HP with ⟨%ha, Hg, Hsr, Hs, Ho, Hbs, Hro, Hvt, Hh⟩
    iunfold roData at Hro
    icases Hro with ⟨He, Hw, Hk⟩
    iframe Hg Hsr Hs Ho Hbs He Hw Hk Hvt Hh
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨-, %hrs, Hg, Hs, Hvt, Hsr, Hbs, He, Hw, Hk, %p, %cap, W0, W4, W8, W12, Hstr⟩
    iunfold post66
    iframe Hg Hs Hbs Hvt
    isplitr
    · ipureintro; exact hrs
    isplitl [Hsr]
    · iexists ptr
      iexists UInt32.ofNat bs.length
      iexists 0
      iexact Hsr
    isplitl [He Hw Hk]
    · iunfold roData
      iframe He Hw Hk
    iunfold strRes at Hstr
    icases Hstr with ⟨%mlen', %F', %⟨hp, hcap, -⟩, Hbytes, Hblk, Hh⟩
    iunfold okAt
    iexists p
    iexists cap
    iexists mlen'
    iexists F'
    iframe W0 W4 W8 W12 Hbytes Hblk Hh
    ipureintro; exact ⟨hp, hcap⟩
  iexact S

/-- 65's precondition: its own 16 bytes of stack, then 66's (`S` bytes below them). -/
def pre65 (S : Nat) (gt : GlobalType) (sp out ptr idx : UInt32) (bs ob : List UInt8) (hl F : Nat)
    (live : List (Nat × Nat)) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗
    stk 0 (sp.toNat - 16) 16 ∗ (stk 0 (sp.toNat - 16 - S) S ∗ 0 ↦[wms][ out.toNat ] ob ∗
      0 ↦[wms][ ptr.toNat ] bs ∗ roData 0 ∗ vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F))

/-- 65's postcondition, with the result `res` at `out`. -/
def post65 (S : Nat) (gt : GlobalType) (sp ptr idx : UInt32) (bs : List UInt8) (res : IProp GF)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 16) 16 ∗
    (stk 0 (sp.toNat - 16 - S) S ∗ 0 ↦[wms][ ptr.toNat ] bs ∗ roData 0 ∗ vt 0 1057464 idx 0 578 ∗ res))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- 65 from a specification of 66 in the form of the contracts (`pre66`, `post66`) at `sp - 16`. -/
theorem f65_of_spec (S : Nat) (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 65 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType) (sp out ptr idx : UInt32) (bs ob : List UInt8)
    (hl F : Nat) (live : List (Nat × Nat)) (hsp : 16 ≤ sp.toNat) (K : Nat) (res : IProp GF)
    (h66 : ⊢ (codeCtx (GF := GF) cfg h0 -∗
      MFunSpec (GF := GF) cfg.wasm lim (d + 1) types[14]! 0 wInst f66 Cg
        (pre66 S gt (sp - 16) out (sp - 16) ptr idx bs ob hl F live) (fun _ => K)
        (post66 S gt (sp - 16) (sp - 16) ptr idx bs res))) :
    codeCtx (GF := GF) cfg h0 ⊢
      MFunSpec (GF := GF) cfg.wasm lim d types[31]! 0 wInst f65 Cg
        (pre65 S gt sp out ptr idx bs ob hl F live) (fun _ => 45 * cfg.wasm.regularOpCost + K)
        (post65 S gt sp ptr idx bs res) := by
  delta pre66 post66 at h66
  iintro #Hctx
  ihave #S66 := h66 $$ Hctx
  ihave #Hc := Hctx
  iunfold codeCtx at Hc
  icases Hc with ⟨#HF, #Hi, -⟩
  ihave #F66 : (66 ↪[wf] FuncInst.wasm types[14]! 0 f66 : IProp GF) $$ []
  · iapply InitialState.wasmLeaf cfg h0 66 _ _ (by decide) (by decide) (by kernel_rfl) (by rfl)
    iexact HF
  ihave #F644 : (644 ↪[wf] FuncInst.wasm types[31]! 0 f644 : IProp GF) $$ []
  · iapply InitialState.wasmLeaf cfg h0 644 _ _ (by decide) (by decide) (by kernel_rfl) (by rfl)
    iexact HF
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have r := f65_of_66 (GF := GF) cfg.wasm lim d types[31]! (by rfl) 0 wInst 0 0
    (Interface.wInst_ifaceMod.mem) (Interface.wInst_ifaceMod.glob) 66 644
    (Interface.wInst_ifaceMod.funcs 66 (by decide)) (Interface.wInst_ifaceMod.funcs 644 (by decide))
    (by omega) Cg gt sp out ptr (UInt32.ofNat bs.length) hsp
    iprop(stk 0 ((sp - 16).toNat - S) S ∗ 0 ↦[wms][ out.toNat ] ob ∗ 0 ↦[wms][ ptr.toNat ] bs ∗ roData 0 ∗
      vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F) K
    (fun _ => iprop(stk 0 ((sp - 16).toNat - S) S ∗ 0 ↦[wms][ ptr.toNat ] bs ∗ roData 0 ∗
      vt 0 1057464 idx 0 578 ∗ res))
  delta pre65 post65
  rw [h16] at r
  iapply r
  iframe F644 F66 Hi
  rw [h16]
  iexact S66

/-- **`serde_json::from_slice` (65), accepting**: from the accepting contract with 400 bytes of
stack, `Ok(a)` at `out` with 416 bytes of stack, within `45·c + (K0 + K1 · len)·c + X`. -/
theorem f65_accept (K0 K1 X : Nat) (hc : AcceptContract (GF := GF) 400 K0 K1 X)
    (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat) (hd : d + 65 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp out ptr idx : UInt32) (bs ob : List UInt8) (hl F : Nat)
    (live : List (Nat × Nat)) (a : WNear.AccountId) (hS : 416 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hob : ob.length = 16) (hr : roomFor4 hl 2048 20)
    (hdec : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a))
    (hcal : AcceptCallees (GF := GF) cfg h0 lim Cg gt (sp - 16 - 64) ptr idx bs F K0 K1 X) :
    codeCtx (GF := GF) cfg h0 ⊢
      MFunSpec (GF := GF) cfg.wasm lim d types[31]! 0 wInst f65 Cg
        (pre65 400 gt sp out ptr idx bs ob hl F live)
        (fun _ => 45 * cfg.wasm.regularOpCost + ((K0 + K1 * bs.length) * cfg.wasm.regularOpCost + X))
        (post65 400 gt sp ptr idx bs (okAt 0 out a live)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  exact f65_of_spec 400 cfg h0 lim d hd Cg gt sp out ptr idx bs ob hl F live (by omega) _ _
    (hc cfg h0 lim (d + 1) (by omega) Cg gt (sp - 16) out (sp - 16) ptr idx bs ob hl F live a (by omega)
      (by omega) hptr hlen hout hob (by omega) hr hdec hcal)

/-- **`serde_json::from_slice` (65), rejecting**: from the rejecting contract with 400 bytes of
stack, `Err(box)` at `out` with 416 bytes of stack, at some finite cost. -/
theorem f65_reject (hc : RejectContract (GF := GF) 400)
    (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat) (hd : d + 65 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp out ptr idx : UInt32) (bs ob : List UInt8) (hl F : Nat)
    (live : List (Nat × Nat)) (hS : 416 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28) (hout : out.toNat + 16 ≤ 2 ^ 32)
    (hob : ob.length = 16) (hr : roomFor4 hl 2048 20)
    (hdec : WNear.Call.decode "ft_balance_of" bs = none) :
    ∃ K : Nat, codeCtx (GF := GF) cfg h0 ⊢
      MFunSpec (GF := GF) cfg.wasm lim d types[31]! 0 wInst f65 Cg
        (pre65 400 gt sp out ptr idx bs ob hl F live) (fun _ => K)
        (post65 400 gt sp ptr idx bs (errAt 0 out live)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  obtain ⟨K, hK⟩ := hc cfg h0 lim (d + 1) (by omega) Cg gt (sp - 16) out (sp - 16) ptr idx bs ob hl F live
    (by omega) (by omega) hptr hlen hout hob (by omega) hr hdec
  exact ⟨_, f65_of_spec 400 cfg h0 lim d hd Cg gt sp out ptr idx bs ob hl F live (by omega) _ _ hK⟩


open WNear.Binary.InitialState in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The code `parse_str` (646) runs on a key without escapes, from the store's function cells. -/
theorem code646_of (cfg : RuntimeConfig) (h : NearState) :
    codeCtx (GF := GF) cfg h ⊢ SerdeErrBox.errCode 0 2048 0 wInst id ∗
      id 927 ↪[wf] FuncInst.wasm types[31]! 0 f927 ∗ id 657 ↪[wf] FuncInst.wasm types[31]! 0 f657 ∗
      id 647 ↪[wf] FuncInst.wasm types[31]! 0 f647 ∗ id 648 ↪[wf] FuncInst.wasm types[45]! 0 f648 := by
  iintro #Hctx
  iunfold codeCtx at Hctx
  icases Hctx with ⟨#HF, #Hi, #Hm⟩
  simp only [SerdeErrBox.errCode, AllocTwo.code310, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | isplitl [])

/-- **The callees of the accepting path on an input without `\`**: `Hyp646` is proved
(`SerdeKeyNoEsc.hyp646_noesc`, at `SerdeKeyNoEsc.K646`: `300 + 130` per byte), so `AcceptCallees`
holds with `K0 = 1725 + a169`, `X = x`, from the two hypotheses left (`Hyp169`, `Hyp81`), their
linear bounds, and the per-member condition of `SerdeCost.cost66_le` with `a646 = 300`,
`b646 = 130`. -/
theorem acceptCallees_noesc (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (Cg : Nat)
    (gt : GlobalType) (de ptr idx : UInt32) (bs : List UInt8) (F : Nat) (hlen : bs.length + 1 < 2 ^ 28)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hnb : (0x5C : UInt8) ∉ bs)
    (a : WNear.AccountId) (hdec : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a))
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (hdv : SerdeStructModel.Agrees dv (SerdeStructModel.valueAs WNear.account))
    (hign : SerdeStructModel.Agrees ign SerdeStructModel.valueSkip) (K169 K81 : Nat → Nat)
    (h169 : SerdeStructArr.Hyp169 cfg.wasm lim 0 wInst 0 0 0 id Cg gt de ptr idx bs 2048 dv K169 F
      (codeCtx (GF := GF) cfg h0))
    (h81 : SerdeStructObj.Hyp81 cfg.wasm lim 0 wInst 0 0 0 id Cg gt de ptr idx bs 2048 ign K81
      (codeCtx (GF := GF) cfg h0))
    (K1 a169 b169 x a81 b81 : Nat)
    (hL169 : SerdeCost.Lin169 cfg.wasm.regularOpCost K169 dv bs a169 b169 x)
    (hL81 : SerdeCost.Lin81 cfg.wasm.regularOpCost K81 ign bs a81 b81)
    (hK : 130 ≤ K1) (hb169 : b169 ≤ K1) (hb81 : b81 ≤ K1)
    (hM169 : 972 + SerdeKey.cost194 + 300 + 130 + a169 + b169 ≤ 5 * K1)
    (hM81 : 972 + SerdeKey.cost194 + 300 + 130 + a81 + b81 ≤ 5 * K1) :
    AcceptCallees (GF := GF) cfg h0 lim Cg gt de ptr idx bs F (1725 + a169) K1 x := by
  refine ⟨dv, ign, SerdeKeyNoEsc.K646 cfg.wasm bs, K169, K81, hdv, hign, ?_, h169, h81, ?_⟩
  · exact SerdeKeyNoEsc.hyp646_noesc cfg.wasm lim 0 wInst id 0 0 0 Interface.wInst_ifaceMod Cg gt de ptr idx bs
      2048 hlen hptr hde hnb (codeCtx cfg h0) (code646_of cfg h0)
  · exact SerdeCost.cost66_le cfg.wasm _ K169 K81 dv ign bs hdv hign a hdec K1 300 130 a169 b169 x a81 b81
      (SerdeKeyNoEsc.lin646_noesc cfg.wasm bs hnb) hL169 hL81 (by omega) hK hb169 hb81 hM169 hM81

end Proof

end WNear.Binary.FromSliceSpec
