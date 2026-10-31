import Bridge.Functions.BalanceOf297ObjectParser

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.SerdeObjectNoEsc
open Wasm Wasm.Near WNear.Binary
open SerdeRead WNear.SerdeStructModel

theorem ignored_linear (cfg : WasmConfig) (bs : List UInt8) :
    SerdeCost.Lin81 cfg.regularOpCost (SerdeIgnReuse.cost81 cfg bs) WNear.IgnoreShallow.ign1R bs 166 470 := by
  intro j r hj h
  unfold WNear.IgnoreShallow.ign1R at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨r', hskip, hres⟩ := h
  cases hres
  unfold SerdeIgnReuse.cost81
  rw [hskip]

set_option maxHeartbeats 4000000 in
theorem parser_cost_linear (cfg : WasmConfig) (F : Nat) (bs rest : List UInt8) (a : WNear.AccountId) (N : Nat)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) WNear.IgnoreShallow.ign1R N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest)) :
    parserCost cfg F bs rest N ≤ (2215 + 470 * bs.length) * cfg.regularOpCost + SerdeAcctHyp.x169 cfg F := by
  have hdvS : ∀ bs a r, valueAs WNear.account bs = some (a, r) → r <:+ bs :=
    fun _ _ _ h => WNear.JsonSuffix.valueAs_suf _ h
  have hignS : ∀ bs r, WNear.IgnoreShallow.ign1R bs = some ((), r) → r <:+ bs :=
    fun _ _ h => WNear.IgnoreShallow.ign1R_suf h
  have hdvL : ∀ bs a r, valueAs WNear.account bs = some (a, r) → r.length < bs.length :=
    fun _ _ _ h => WNear.JsonSuffix.valueAs_strict _ h
  have hignL : ∀ bs r, WNear.IgnoreShallow.ign1R bs = some ((), r) → r.length < bs.length :=
    fun _ _ h => WNear.IgnoreShallow.ign1R_strict h
  have hR : WNear.SerdeStructLoop.loopRes "account_id" (valueAs WNear.account) WNear.IgnoreShallow.ign1R N true none
      (bs.drop (wsLen bs + 1)) = some (some a, rest) := by
    simpa only [WNear.SerdeStructLoop.loopRes, ite_true] using hloop
  have hstart := SerdeNextKey.getElem_lt ho
  have hb := SerdeCost.objCost_le cfg.regularOpCost (SerdeKeyNoEsc.K646 cfg bs) (SerdeAcctHyp.K169 cfg bs F)
    (SerdeIgnReuse.cost81 cfg bs) (valueAs WNear.account) WNear.IgnoreShallow.ign1R bs 470 300 130 0 208
    (SerdeAcctHyp.x169 cfg F) 166 470 (SerdeKeyNoEsc.lin646_noesc cfg bs hnb)
    (SerdeAcctHyp.lin169_noesc cfg bs hnb F) (ignored_linear cfg bs) hdvS hignS hdvL hignL
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
    N true (wsLen bs + 1) none a rest (by omega) hR
  simp only [ite_true, Option.isNone_none] at hb
  have hr := (SerdeCost.loopRes_suf "account_id" _ _ hdvS hignS hR).length_le
  simp only [List.length_drop] at hr
  have hw := wsLen_le (bs.drop (bs.length - rest.length))
  simp only [List.length_drop] at hw
  have hcoef : 2215 + 96 * wsLen bs + 96 * wsLen (bs.drop (bs.length - rest.length)) +
      470 * (bs.length - rest.length - (wsLen bs + 1)) ≤ 2215 + 470 * bs.length := by omega
  have hpay := Nat.mul_le_mul_right cfg.regularOpCost hcoef
  unfold parserCost SerdeStructObj.costObj
  simp only [List.drop_zero, Nat.zero_add]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hb hpay ⊢
  omega

end WNear.Binary.SerdeObjectNoEsc
