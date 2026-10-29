import Bridge.Functions.FromSliceReject
import Bridge.Functions.SerdeStructObjectEOF
import Bridge.Functions.FromSliceEOF

/-!
# An unfinished object is rejected by the instantiated parser

This discharges the struct rejection specification for an opening brace
followed only by whitespace, and carries it
through 78, 66 and 65. No parser-callee specification is assumed. The result
and finite cost are uniform in the gas ceiling.
-/

namespace WNear.Binary.FromSliceSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.SerdeRead (wsLen)
open NearInterface.Json

/-- The model rejects an opening brace followed only by whitespace. -/
theorem decode_obj_eof (bs : List UInt8) (hb0 : bs[wsLen bs]? = some 0x7B)
    (heof : wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)) = bs.length) :
    WNear.Call.decode "ft_balance_of" bs = none := by
  have hj := SerdeNextKey.getElem_lt hb0
  have hbyte : bs[wsLen bs] = 0x7B := by
    rw [List.getElem?_eq_getElem hj] at hb0
    exact Option.some.inj hb0
  have hstart : skipWhitespace bs = 0x7B :: bs.drop (wsLen bs + 1) := by
    rw [SerdeRead.skipWhitespace_eq, List.drop_eq_getElem_cons hj, hbyte]
  have hrest : skipWhitespace (bs.drop (wsLen bs + 1)) = [] := by
    rw [SerdeRead.skipWhitespace_eq]
    apply List.drop_eq_nil_of_le
    simp only [List.length_drop]
    omega
  have hs : SerdeStructModel.structDe "account_id" (SerdeStructModel.valueAs WNear.account)
      SerdeStructModel.valueSkip bs = none := by
    simp [SerdeStructModel.structDe, hstart, hrest, SerdeStructModel.objLoop,
      WNear.JsonFuel.keyAt]
  rw [SerdeStructModel.decode_balanceOf _ _ (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)]
  simp [SerdeStructModel.fromSlice, hs]

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.InitialState in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The code used by the unfinished-object path, from the instantiated module. -/
theorem objectEOFCode_of (cfg : RuntimeConfig) (h : NearState) :
    codeCtx (GF := GF) cfg h ⊢
      SerdeEnds.endCode 0 2048 0 wInst id ∗ 193 ↪[wf] FuncInst.wasm types[11]! 0 f193 ∗
      326 ↪[wf] FuncInst.wasm types[13]! 0 f326 ∗
      327 ↪[wf] FuncInst.wasm types[13]! 0 f327 ∗
      90 ↪[wf] FuncInst.wasm types[32]! 0 f90 ∗
      92 ↪[wf] FuncInst.wasm types[0]! 0 f92 ∗
      709 ↪[wf] FuncInst.wasm types[32]! 0 f709 ∗ DropVec.dropCode 0 wInst id := by
  iintro #Hctx
  ihave #HE := endCode_of cfg h $$ Hctx
  ihave #HD := dropCode_of cfg h $$ Hctx
  iunfold codeCtx at Hctx
  icases Hctx with ⟨#HF, #Hi, #Hm⟩
  repeat' (first
    | iexact HE
    | iexact HD
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | isplitl [])

/-- The actual `from_slice` (65) rejects an opening brace followed only by whitespace. -/
theorem f65_obj_eof_reject_uniform (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 65 < lim.maxCallDepth) (gt : GlobalType) (sp out ptr idx : UInt32)
    (bs ob : List UInt8) (hl F : Nat) (live : List (Nat × Nat))
    (hS : 416 ≤ sp.toNat) (hal : sp.toNat % 16 = 0)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hlen : bs.length + 1 < 2 ^ 28)
    (hout : out.toNat + 16 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hr : SerdeStructArr.roomS hl 2048) (hb0 : bs[wsLen bs]? = some 0x7B)
    (heof : wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1)) = bs.length) :
    ∀ Cg, codeCtx (GF := GF) cfg h0 ⊢
      MFunSpec cfg.wasm lim d types[31]! 0 wInst f65 Cg
        (pre65 400 gt sp out ptr idx bs ob hl F live)
        (fun _ => 1045 * cfg.wasm.regularOpCost +
          ((4000 + 96 * (wsLen bs + wsLen (bs.drop (wsLen bs + 1)))) * cfg.wasm.regularOpCost + SerdeErrBox.costErr cfg.wasm F (bs.length + 1) +
            SerdeErrBox.costErr cfg.wasm (max F 1) (bs.length + 1)))
        (post65 400 gt sp ptr idx bs (errAt 0 out live)) := by
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have h80 : (sp - 16 - 64).toNat = sp.toNat - 80 := by
    rw [UInt32.toNat_sub_of_le]
    · simp only [h16, UInt32.reduceToNat]; omega
    · simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat, h16]; omega
  apply f65_struct_reject_uniform cfg h0 lim d hd gt sp out ptr idx bs ob hl F live hS hal hptr hlen hout hob hr
    (fun F => (4000 + 96 * (wsLen bs + wsLen (bs.drop (wsLen bs + 1)))) * cfg.wasm.regularOpCost + SerdeErrBox.costErr cfg.wasm F (bs.length + 1) +
            SerdeErrBox.costErr cfg.wasm (max F 1) (bs.length + 1))
  intro Cg
  exact SerdeRej.rej228_obj_eof cfg.wasm lim 0 wInst id 0 0 0 Interface.wInst_ifaceMod Cg gt
    (sp - 16 - 64) ptr idx bs 2048 hlen hptr (by rw [h80]; omega)
    hb0 heof (codeCtx cfg h0) (objectEOFCode_of cfg h0)

end Proof

end WNear.Binary.FromSliceSpec
