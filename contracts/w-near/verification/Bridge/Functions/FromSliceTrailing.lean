import Bridge.Functions.FromSliceReject
import Bridge.Functions.SerdeTrailing

/-!
# The public parser contract for trailing-character rejection

The readers and their cost functions are fixed before the gas ceiling. Once
they parse a struct but leave non-whitespace, 66 and 65 return an error with
uniform finite costs, including the syntax-error allocation and both drops.
-/

namespace WNear.Binary.FromSliceSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRej (errOut)
open WNear.Binary.SerdeStructArr (Hyp169)
open WNear.Binary.SerdeStructObj (Hyp646 Hyp81)
open NearInterface.Json

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 66 rejects trailing characters, uniformly in the gas ceiling. -/
theorem trailing_reject_uniform (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 64 < lim.maxCallDepth) (gt : GlobalType) (sp out rd ptr idx : UInt32)
    (bs ob : List UInt8) (hl F : Nat) (live : List (Nat × Nat))
    (hS : 400 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hob : ob.length = 16) (hrd : rd.toNat + 12 ≤ 2 ^ 32)
    (hr : SerdeStructArr.roomS hl 2048)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (K646 K169 K81 : Nat → Nat)
    (h646 : ∀ Cg, Hyp646 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 64) ptr idx bs 2048 K646
      (codeCtx (GF := GF) cfg h0))
    (h169 : ∀ Cg, Hyp169 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 64) ptr idx bs 2048 dv K169 F
      (codeCtx (GF := GF) cfg h0))
    (h81 : ∀ Cg, Hyp81 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 64) ptr idx bs 2048 ign K81
      (codeCtx (GF := GF) cfg h0))
    (hdv0 : dv [] = none)
    (hdvs : ∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r)
    (higns : ∀ j r, j ≤ bs.length → ign (bs.drop j) = some ((), r) → bs.drop (bs.length - r.length) = r)
    (hstrs : ∀ q k r, q ≤ bs.length → stringBody (bs.drop q) [] = some (some k, r) → bs.drop (bs.length - r.length) = r)
    (a : WNear.AccountId) (r : List UInt8)
    (hstruct : SerdeStructModel.structDe "account_id" dv ign bs = some (a, r))
    (htrailing : skipWhitespace r ≠ []) (hsuf : bs.drop (bs.length - r.length) = r) :
    ∀ Cg, ⊢ (codeCtx (GF := GF) cfg h0 -∗
      MFunSpec cfg.wasm lim d types[14]! 0 wInst f66 Cg
        (pre66 400 gt sp out rd ptr idx bs ob hl F live)
        (fun _ => (2000 + 96 * r.length) * cfg.wasm.regularOpCost +
          SerdeStruct78.costS cfg.wasm K646 K169 K81 dv ign bs +
          SerdeErrBox.costErr cfg.wasm (2 ^ 32) (bs.length + 1))
        (post66 400 gt sp rd ptr idx bs (errAt 0 out live))) := by
  intro Cg
  have s := SerdeRej.f66_trailing (GF := GF) cfg.wasm lim d types[14]! rfl 0 wInst id 0 0 0
    Interface.wInst_ifaceMod (by omega) Cg gt sp out rd ptr idx ob bs 2048 hl F live hob hout hrd hlen hptr hS
    (by omega) hr dv ign K646 K169 K81 F (codeCtx cfg h0) (h646 Cg) (h169 Cg) (h81 Cg) (Nat.le_refl F)
    hdv0 hdvs higns hstrs a r hstruct htrailing hsuf
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

/-- The same trailing-character rejection through the public `from_slice` (65). -/
theorem f65_trailing_reject_uniform (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 65 < lim.maxCallDepth) (gt : GlobalType) (sp out ptr idx : UInt32)
    (bs ob : List UInt8) (hl F : Nat) (live : List (Nat × Nat))
    (hS : 416 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hr : SerdeStructArr.roomS hl 2048)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (K646 K169 K81 : Nat → Nat)
    (h646 : ∀ Cg, Hyp646 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 16 - 64) ptr idx bs 2048 K646
      (codeCtx (GF := GF) cfg h0))
    (h169 : ∀ Cg, Hyp169 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 16 - 64) ptr idx bs 2048 dv K169 F
      (codeCtx (GF := GF) cfg h0))
    (h81 : ∀ Cg, Hyp81 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 16 - 64) ptr idx bs 2048 ign K81
      (codeCtx (GF := GF) cfg h0))
    (hdv0 : dv [] = none)
    (hdvs : ∀ j a r, j ≤ bs.length → dv (bs.drop j) = some (a, r) → bs.drop (bs.length - r.length) = r)
    (higns : ∀ j r, j ≤ bs.length → ign (bs.drop j) = some ((), r) → bs.drop (bs.length - r.length) = r)
    (hstrs : ∀ q k r, q ≤ bs.length → stringBody (bs.drop q) [] = some (some k, r) → bs.drop (bs.length - r.length) = r)
    (a : WNear.AccountId) (r : List UInt8)
    (hstruct : SerdeStructModel.structDe "account_id" dv ign bs = some (a, r))
    (htrailing : skipWhitespace r ≠ []) (hsuf : bs.drop (bs.length - r.length) = r) :
    ∀ Cg, codeCtx (GF := GF) cfg h0 ⊢
      MFunSpec cfg.wasm lim d types[31]! 0 wInst f65 Cg
        (pre65 400 gt sp out ptr idx bs ob hl F live)
        (fun _ => (2045 + 96 * r.length) * cfg.wasm.regularOpCost +
          SerdeStruct78.costS cfg.wasm K646 K169 K81 dv ign bs +
          SerdeErrBox.costErr cfg.wasm (2 ^ 32) (bs.length + 1))
        (post65 400 gt sp ptr idx bs (errAt 0 out live)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h66 := trailing_reject_uniform (GF := GF) cfg h0 lim (d + 1) (by omega) gt (sp - 16) out
    (sp - 16) ptr idx bs ob hl F live (by omega) (by omega) hptr hlen hout hob (by omega) hr
    dv ign K646 K169 K81 h646 h169 h81 hdv0 hdvs higns hstrs a r hstruct htrailing hsuf
  intro Cg
  have hs := f65_of_spec 400 cfg h0 lim d hd Cg gt sp out ptr idx bs ob hl F live (by omega)
    ((2000 + 96 * r.length) * cfg.wasm.regularOpCost + SerdeStruct78.costS cfg.wasm K646 K169 K81 dv ign bs +
      SerdeErrBox.costErr cfg.wasm (2 ^ 32) (bs.length + 1)) (errAt 0 out live) (h66 Cg)
  have hcost : 45 * cfg.wasm.regularOpCost +
      ((2000 + 96 * r.length) * cfg.wasm.regularOpCost + SerdeStruct78.costS cfg.wasm K646 K169 K81 dv ign bs +
        SerdeErrBox.costErr cfg.wasm (2 ^ 32) (bs.length + 1)) =
      (2045 + 96 * r.length) * cfg.wasm.regularOpCost + SerdeStruct78.costS cfg.wasm K646 K169 K81 dv ign bs +
        SerdeErrBox.costErr cfg.wasm (2 ^ 32) (bs.length + 1) := by ring
  simpa only [hcost] using hs

end Proof

end WNear.Binary.FromSliceSpec
