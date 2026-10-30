import Bridge.Functions.FromSliceProof
import Bridge.Functions.SerdeAcctHyp

/-!
# `ft_balance_of`'s parser on an input without escapes: only `Hyp81` left (M6)

`FromSliceProof.acceptCallees_noesc` left `Hyp169` and `Hyp81`. `SerdeAcctHyp.hyp169_noesc` proves
`Hyp169` for the model's own reader `valueAs account` on an input with no `\` byte, at the cost
`K169 cfg bs Fb` with `Lin169` constants `a = 0`, `b = 208`, `x169 cfg F` (`lin169_noesc`). So:

* `code169_of`: 169's code from the store's function cells (`codeCtx`);
* `acceptCallees_noesc81`: on an input without `\`, `AcceptCallees … 1725 K1 (x169 cfg F)` holds from
  `Hyp81` (for a reader `ign` that agrees with the model) and its linear bound `Lin81 a81 b81` alone,
  when `208 ≤ K1` (whitespace `96`, keys `130`, the account id `208` per byte), `b81 ≤ K1` and
  `1714 + a81 + b81 ≤ 5·K1` (a member with an ignored value). The account id's member needs
  `1714 + 208 ≤ 5·K1`, i.e. `K1 ≥ 385`.
* `acceptContract_noesc81`: the accepting contract's conclusion on such an input, with the stack
  of 400 bytes, the room `roomS`, and only `Hyp81` and its bound as premises.
-/

namespace WNear.Binary.FromSliceSpec

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.SerdeErrBox (roomFor4)

section Proof

variable {GF : BundledGFunctors} [WasmGS NearState GF]

open WNear.Binary.InitialState in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The code `ValidAccountId::deserialize` (169) runs on an accepted account id, from the store's
function cells. -/
theorem code169_of (cfg : RuntimeConfig) (h : NearState) :
    codeCtx (GF := GF) cfg h ⊢ SerdeAccountId.code169 0 2048 0 wInst id := by
  iintro #Hctx
  iunfold codeCtx at Hctx
  icases Hctx with ⟨#HF, #Hi, #Hm⟩
  simp only [SerdeAccountId.code169, SerdeDeStr.code380, SerdeString.strCode, SerdeErrBox.errCode,
    AllocTwo.code310, id]
  repeat' (first
    | iexact Hi
    | iexact Hm
    | (iapply wasmLeaf cfg h _ _ _ ?_ ?_ ?_ ?_ <;> first | iexact HF | decide | kernel_rfl | rfl)
    | isplitl [])

/-- **The callees of the accepting path on an input without `\`, `Hyp169` proved**: `AcceptCallees`
holds with `K0 = 1725`, `X = x169 cfg.wasm F`, from `Hyp81`, its linear bound, and the per-member
conditions. -/
theorem acceptCallees_noesc81 (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (Cg : Nat)
    (gt : GlobalType) (de ptr idx : UInt32) (bs : List UInt8) (F : Nat) (hlen : bs.length + 1 < 2 ^ 28)
    (hptr : ptr.toNat + bs.length < 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) (hnb : (0x5C : UInt8) ∉ bs)
    (a : WNear.AccountId) (hdec : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a))
    (ign : List UInt8 → Option (Unit × List UInt8))
    (hign : SerdeStructModel.Agrees ign SerdeStructModel.valueSkip) (K81 : Nat → Nat)
    (h81 : SerdeStructObj.Hyp81 cfg.wasm lim 0 wInst 0 0 0 id Cg gt de ptr idx bs 2048 ign K81
      (codeCtx (GF := GF) cfg h0))
    (K1 a81 b81 : Nat) (hL81 : SerdeCost.Lin81 cfg.wasm.regularOpCost K81 ign bs a81 b81)
    (hK : 208 ≤ K1) (hb81 : b81 ≤ K1) (hK5 : 942 + SerdeKey.cost194 + 300 + 130 + 208 ≤ 5 * K1)
    (hM81 : 942 + SerdeKey.cost194 + 300 + 130 + a81 + b81 ≤ 5 * K1) :
    AcceptCallees (GF := GF) cfg h0 lim Cg gt de ptr idx bs F 1725 K1 (SerdeAcctHyp.x169 cfg.wasm F) := by
  have h169 := SerdeAcctHyp.hyp169_noesc (GF := GF) cfg.wasm lim 0 wInst id 0 0 0 Interface.wInst_ifaceMod Cg gt de ptr
    idx bs 2048 hlen hptr hde hnb F (codeCtx cfg h0) (code169_of cfg h0)
  have := acceptCallees_noesc (GF := GF) cfg h0 lim Cg gt de ptr idx bs F hlen hptr hde hnb a hdec
    (SerdeStructModel.valueAs WNear.account) ign (fun _ => Or.inl rfl) hign
    (SerdeAcctHyp.K169 cfg.wasm bs F) K81 h169 h81 K1 0 208 (SerdeAcctHyp.x169 cfg.wasm F) a81 b81
    (SerdeAcctHyp.lin169_noesc cfg.wasm bs hnb F) hL81 (by omega) hK hb81 (by omega) hM81
  simpa using this

/-- **The accepting contract on an input without `\`, only `Hyp81` left**: 66 returns `Ok(a)` within
`(1725 + K1 · len) · c + x169 cfg F`, given `Hyp81` for a reader that agrees with the model and its
linear bound. -/
theorem acceptContract_noesc81 (K1 : Nat) (cfg : RuntimeConfig) (h0 : NearState) (lim : ExecLimits) (d : Nat)
    (hd : d + 64 < lim.maxCallDepth) (Cg : Nat) (gt : GlobalType) (sp out rd ptr idx : UInt32)
    (bs ob : List UInt8) (hl F : Nat) (live : List (Nat × Nat)) (a : WNear.AccountId)
    (hS : 400 ≤ sp.toNat) (hal : sp.toNat % 16 = 0) (hptr : ptr.toNat + bs.length < 2 ^ 32)
    (hlen : bs.length + 1 < 2 ^ 28) (hout : out.toNat + 16 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hrd : rd.toNat + 12 ≤ 2 ^ 32) (hr : SerdeStructArr.roomS hl 2048)
    (hdec : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a)) (hnb : (0x5C : UInt8) ∉ bs)
    (ign : List UInt8 → Option (Unit × List UInt8))
    (hign : SerdeStructModel.Agrees ign SerdeStructModel.valueSkip) (K81 : Nat → Nat)
    (h81 : SerdeStructObj.Hyp81 cfg.wasm lim 0 wInst 0 0 0 id Cg gt (sp - 64) ptr idx bs 2048 ign K81
      (codeCtx (GF := GF) cfg h0))
    (a81 b81 : Nat) (hL81 : SerdeCost.Lin81 cfg.wasm.regularOpCost K81 ign bs a81 b81)
    (hK : 208 ≤ K1) (hb81 : b81 ≤ K1) (hK5 : 942 + SerdeKey.cost194 + 300 + 130 + 208 ≤ 5 * K1)
    (hM81 : 942 + SerdeKey.cost194 + 300 + 130 + a81 + b81 ≤ 5 * K1) :
    ⊢ (codeCtx (GF := GF) cfg h0 -∗
      MFunSpec (GF := GF) cfg.wasm lim d types[14]! 0 wInst f66 Cg
        (pre66 400 gt sp out rd ptr idx bs ob hl F live)
        (fun _ => (1725 + K1 * bs.length) * cfg.wasm.regularOpCost + SerdeAcctHyp.x169 cfg.wasm F)
        (post66 400 gt sp rd ptr idx bs (okAt 0 out a live))) := by
  have hlt := sp.toNat_lt
  have h64 : (sp - 64).toNat = sp.toNat - 64 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  exact acceptContract 1725 K1 (SerdeAcctHyp.x169 cfg.wasm F) cfg h0 lim d hd Cg gt sp out rd ptr idx bs ob hl F
    live a hS hal hptr hlen hout hob hrd hr hdec
    (acceptCallees_noesc81 cfg h0 lim Cg gt (sp - 64) ptr idx bs F hlen hptr (by omega) hnb a hdec ign hign K81
      h81 K1 a81 b81 hL81 hK hb81 hK5 hM81)

end Proof

end WNear.Binary.FromSliceSpec
