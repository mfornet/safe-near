import Bridge.Functions.FromSliceReject
import Bridge.Functions.SerdeStructEOF

/-!
# Empty and whitespace-only arguments are rejected by the instantiated parser

This discharges the struct rejection specification for EOF, and carries it
through 78, 66 and 65. No parser-callee specification is assumed. The result
and finite cost are uniform in the gas ceiling.
-/

namespace WNear.Binary.FromSliceSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.SerdeRead (wsLen)
open NearInterface.Json

/-- The model rejects input consisting only of whitespace. -/
theorem decode_eof (bs : List UInt8) (heof : skipWhitespace bs = []) :
    WNear.Call.decode "ft_balance_of" bs = none := by
  have hs : SerdeStructModel.structDe "account_id" (SerdeStructModel.valueAs WNear.account)
      SerdeStructModel.valueSkip bs = none := by
    apply SerdeStructModel.structDe_other
    · intro r; rw [heof]; simp
    · intro r; rw [heof]; simp
  rw [SerdeStructModel.decode_balanceOf _ _ (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)]
  simp [SerdeStructModel.fromSlice, hs]

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The punctuation/error code from the parser's instantiated code cells. -/
theorem endCode_of (cfg : RuntimeConfig) (h : NearState) :
    codeCtx (GF := GF) cfg h ⊢ SerdeEnds.endCode 0 2048 0 wInst id := by
  iintro #Hctx
  ihave #H := code66_of cfg h $$ Hctx
  iunfold SerdeFromTrait.code66 at H
  icases H with ⟨#H, _⟩
  iunfold SerdeNextKey.code193 at H
  icases H with ⟨#H, _⟩
  iexact H

/-- The actual `from_slice` (65) rejects empty or whitespace-only arguments. -/
theorem f65_eof_reject_uniform (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 65 < lim.maxCallDepth) (gt : GlobalType) (sp out ptr idx : UInt32)
    (bs ob : List UInt8) (hl F : Nat) (live : List (Nat × Nat))
    (hS : 416 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hr : SerdeStructArr.roomS hl 2048) (heof : skipWhitespace bs = []) :
    ∀ Cg, codeCtx (GF := GF) cfg h0 ⊢
      MFunSpec cfg.wasm lim d types[31]! 0 wInst f65 Cg
        (pre65 400 gt sp out ptr idx bs ob hl F live)
        (fun _ => 1045 * cfg.wasm.regularOpCost +
          ((500 + 96 * wsLen bs) * cfg.wasm.regularOpCost + SerdeErrBox.costErr cfg.wasm F (bs.length + 1)))
        (post65 400 gt sp ptr idx bs (errAt 0 out live)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h80 : (sp - 16 - 64).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le]
    · simp only [h16, UInt32.reduceToNat]; omega
    · simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat, h16]; omega
  apply f65_struct_reject_uniform cfg h0 lim d hd gt sp out ptr idx bs ob hl F live hS hal hptr hlen hout hob hr
    (fun F => (500 + 96 * wsLen bs) * cfg.wasm.regularOpCost + SerdeErrBox.costErr cfg.wasm F (bs.length + 1))
  intro Cg
  exact SerdeRej.rej228_eof cfg.wasm lim 0 wInst id 0 0 0 Interface.wInst_ifaceMod Cg gt
    (sp - 16 - 64) ptr idx bs 2048 hlen hptr (by rw [h80]; omega)
    (SerdeFromTrait.wsLen_all heof) (codeCtx cfg h0) (endCode_of cfg h0)

end Proof

end WNear.Binary.FromSliceSpec
