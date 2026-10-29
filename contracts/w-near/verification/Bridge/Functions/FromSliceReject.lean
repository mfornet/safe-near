import Bridge.Functions.FromSliceProof
import Bridge.Functions.SerdeFromReject

/-!
# Instantiated parser rejection through the struct error branch

The uniform cost is chosen before the gas ceiling. This connects the conditional
228 rejection specification to 66's public pre/postconditions. The complete
`RejectContract` still needs 228's rejecting cases and trailing-character errors.
-/

namespace WNear.Binary.FromSliceSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRej (Rej228 errOut)
open WNear.SerdeStructModel (Agrees valueAs valueSkip)

/-- Every rejected input fails within the struct or has non-whitespace left after it. -/
theorem decode_reject_cases {dv : List UInt8 → Option (WNear.AccountId × List UInt8)}
    {ign : List UInt8 → Option (Unit × List UInt8)}
    (hdv : Agrees dv (valueAs WNear.account)) (hign : Agrees ign valueSkip)
    {bs : List UInt8} (hdec : WNear.Call.decode "ft_balance_of" bs = none) :
    SerdeStructModel.structDe "account_id" dv ign bs = none ∨
      ∃ a r, SerdeStructModel.structDe "account_id" dv ign bs = some (a, r) ∧
        NearInterface.Json.skipWhitespace r ≠ [] := by
  rw [SerdeStructModel.decode_balanceOf dv ign hdv hign bs] at hdec
  cases hs : SerdeStructModel.structDe "account_id" dv ign bs with
  | none => exact Or.inl rfl
  | some ar =>
    obtain ⟨a, r⟩ := ar
    right
    refine ⟨a, r, rfl, ?_⟩
    intro he
    simp [SerdeStructModel.fromSlice, hs, SerdeStructModel.endOk, he] at hdec

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.InitialState in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The deallocation code used after a rejected struct. -/
theorem dropCode_of (cfg : RuntimeConfig) (h : NearState) :
    codeCtx (GF := GF) cfg h ⊢ DropVec.dropCode 0 wInst id := by
  iintro #Hctx
  iunfold codeCtx at Hctx
  icases Hctx with ⟨#HF, #Hi, #Hm⟩
  simp only [DropVec.dropCode, id]
  repeat' (first
    | iexact Hi
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | isplitl [])

/-- From a uniform struct rejection proof to 66's public contract, at one fixed cost. -/
theorem struct_reject_uniform (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 64 < lim.maxCallDepth) (gt : GlobalType) (sp out rd ptr idx : UInt32)
    (bs ob : List UInt8) (hl F : Nat) (live : List (Nat × Nat))
    (hS : 400 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hob : ob.length = 16) (hrd : rd.toNat + 12 ≤ 2 ^ 32)
    (hr : SerdeStructArr.roomS hl 2048) (K : Nat → Nat)
    (h228 : ∀ Cg, Rej228 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 64) ptr idx bs 2048 K
      (codeCtx (GF := GF) cfg h0)) :
    ∀ Cg, ⊢ (codeCtx (GF := GF) cfg h0 -∗
      MFunSpec cfg.wasm lim d types[14]! 0 wInst f66 Cg
        (pre66 400 gt sp out rd ptr idx bs ob hl F live)
        (fun _ => 1000 * cfg.wasm.regularOpCost + K F)
        (post66 400 gt sp rd ptr idx bs (errAt 0 out live))) := by
  intro Cg
  have s := SerdeRej.f66_struct_rej (GF := GF) cfg.wasm lim d types[14]! rfl 0 wInst id 0 0 0
    Interface.wInst_ifaceMod (by omega) Cg gt sp out rd ptr idx ob bs 2048 hl F live hob hout hrd hlen hptr hS
    (by omega) hr K (codeCtx cfg h0) (h228 Cg)
  simp only [id] at s
  iintro #Hctx
  ihave #C66 := code66_of cfg h0 $$ Hctx
  ihave #HD := dropCode_of cfg h0 $$ Hctx
  ihave #S := s $$ [C66 HD Hctx]
  · iframe C66 HD Hctx
  clear s
  iapply (AllocFresh.MFunSpec_frame (Fr := iprop(emp))
    (P := fun args => iprop(⌜args = [.i32 out, .i32 rd]⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 400) 400 ∗
      vt 0 1057464 idx 0 578 ∗ heapInv 0 2048 hl live F ∗ 0 ↦[wms][ out.toNat ] ob ∗
      sliceRead 0 rd ptr (UInt32.ofNat bs.length) 0 ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ 0 ↦[wms][ 1048576 ] SerdeIdent.identBytes))
    (Q := fun _ rs => iprop(⌜rs = []⌝ ∗ 0 ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk 0 (sp.toNat - 400) 400 ∗
      vt 0 1057464 idx 0 578 ∗ sliceRead 0 rd ptr (UInt32.ofNat bs.length) 0 ∗ 0 ↦[wms][ ptr.toNat ] bs ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes ∗ 0 ↦[wms][ 1048576 ] SerdeIdent.identBytes ∗
      errOut 0 2048 out live)) ?hP ?hQ)
  case hP =>
    intro args
    iintro HP
    iunfold pre66 at HP
    icases HP with ⟨%ha, Hg, Hsr, Hs, Ho, Hbs, Hro, Hvt, Hh⟩
    iunfold roData at Hro
    icases Hro with ⟨He, Hw, Hk, Hid⟩
    iframe Hg Hsr Hs Ho Hbs He Hw Hk Hid Hvt Hh
    ipureintro; exact ha
  case hQ =>
    intro args rs
    iintro ⟨_, %hrs, Hg, Hs, Hvt, Hsr, Hbs, He, Hw, Hk, Hid, HE⟩
    iunfold post66
    iframe Hg Hs Hbs Hvt
    isplitr
    · ipureintro; exact hrs
    isplitl [Hsr]
    · iexists ptr, UInt32.ofNat bs.length, 0
      iexact Hsr
    isplitl [He Hw Hk Hid]
    · iunfold roData
      iframe He Hw Hk Hid
    iunfold errOut at HE
    iunfold errAt
    iexact HE
  iexact S

/-- The same uniform rejection branch through `serde_json::from_slice` (65). -/
theorem f65_struct_reject_uniform (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 65 < lim.maxCallDepth) (gt : GlobalType) (sp out ptr idx : UInt32)
    (bs ob : List UInt8) (hl F : Nat) (live : List (Nat × Nat))
    (hS : 416 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hr : SerdeStructArr.roomS hl 2048) (K : Nat → Nat)
    (h228 : ∀ Cg, Rej228 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 16 - 64) ptr idx bs 2048 K
      (codeCtx (GF := GF) cfg h0)) :
    ∀ Cg, codeCtx (GF := GF) cfg h0 ⊢
      MFunSpec cfg.wasm lim d types[31]! 0 wInst f65 Cg
        (pre65 400 gt sp out ptr idx bs ob hl F live)
        (fun _ => 1045 * cfg.wasm.regularOpCost + K F)
        (post65 400 gt sp ptr idx bs (errAt 0 out live)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h66 := struct_reject_uniform (GF := GF) cfg h0 lim (d + 1) (by omega) gt (sp - 16) out
    (sp - 16) ptr idx bs ob hl F live (by omega) (by omega) hptr hlen hout hob (by omega) hr K h228
  intro Cg
  have hs := f65_of_spec 400 cfg h0 lim d hd Cg gt sp out ptr idx bs ob hl F live (by omega)
    (1000 * cfg.wasm.regularOpCost + K F) (errAt 0 out live) (h66 Cg)
  have hcost : 45 * cfg.wasm.regularOpCost + (1000 * cfg.wasm.regularOpCost + K F) =
      1045 * cfg.wasm.regularOpCost + K F := by omega
  simpa only [hcost] using hs

end Proof

end WNear.Binary.FromSliceSpec
