import Bridge.Methods.FtBalanceOfCopiedRun

/-! Model agreement of the two-read absent-account postcondition, including storage-stake failure. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface ContractModel WNear WNear.Binary.FtTotalSupplyMethod in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem copied_agreement_of_represents (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (a : WNear.AccountId) (tr : Near.TrieOverlay.State) (hrep : (wnear cfg).Represents raw st) (hwf : ctx.WF raw)
    (hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S))
    (hnone : (hostOf ctx raw).storage (copiedKey a) = none)
    (h0 : NearState) (hh0 : eraseP h0 = eraseP (hostOf ctx raw)) :
    ∀ e, copiedMethodPost a tr h0 e →
      AgreesWith (wnear cfg) ctx raw e ((wnear cfg).step ctx st (.ftBalanceOf a)) := by
  intro e hp
  have hf : ∀ {α : Type} (f : NearState → α), (∀ x, f (eraseP x) = f x) → f h0 = f (hostOf ctx raw) :=
    fun f hfe => eraseP_field hh0 f hfe
  -- the represented state
  cases st with
  | none =>
    have h0 : raw = ∅ := hrep
    rw [hostOf_storage, h0] at hval
    simp at hval
  | some S' =>
    obtain ⟨hinv, hraw⟩ := (show Inv cfg S' ∧ raw = encode S' from hrep)
    obtain ⟨reg, hreg, hstep⟩ := FtBalanceOfMethod.account_lookup_and_step cfg ctx raw S' hwf hraw hinv.toWF h0 hh0 a.toNear
    simp only [WNear.AccountId.ofNear_toNear] at hstep
    have hnone0 : h0.storage (copiedKey a) = none := by rw [hf NearState.storage (fun _ => rfl)]; exact hnone
    have hnreg : reg = none := by
      have hlen : a.val.toUTF8.toList.length = a.val.utf8ByteSize := by
        rw [Wasm.ByteEncoding.byteArray_toList_length]; simp [String.toUTF8_eq_toByteArray]
      change h0.storage (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList)) = _ at hreg
      rw [hlen, hnone0] at hreg
      cases reg with
      | none => rfl
      | some pair => simp only [Option.map_some] at hreg; cases hreg
    simp only [hnreg, Option.map_none, Option.getD_none] at hstep
    -- the final host's fields
    have hbal : e.context.accountBalance = ctx.balance + ctx.attached :=
      (copied_post_field (fun x => x.context.accountBalance) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) hp).trans
        (hf (fun x => x.context.accountBalance) fun _ => rfl)
    have hsu : e.context.storageUsage = UInt64.ofNat ctx.storageUsage :=
      (copied_post_field (fun x => x.context.storageUsage) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
        (fun _ _ => rfl) hp).trans
        (hf (fun x => x.context.storageUsage) fun _ => rfl)
    have hsto : e.storage = (hostOf ctx raw).storage :=
      (copied_post_field NearState.storage (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.storage fun _ => rfl)
    have hkeys : e.storageKeys = (hostOf ctx raw).storageKeys :=
      (copied_post_field NearState.storageKeys (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.storageKeys fun _ => rfl)
    have hlogs : e.logs = [] :=
      (copied_post_field NearState.logs (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) hp).trans
        (hf NearState.logs fun _ => rfl)
    have hfin : finalStorage e = finalStorage (hostOf ctx raw) := by
      simp only [finalStorage, hsto, hkeys]
    have hroom := hwf.usage_room
    have hge := hwf.usage_ge
    have hsuN : e.context.storageUsage.toNat = ctx.storageUsage := by
      rw [hsu, UInt64.toNat_ofNat_of_lt' (by show _ < 2 ^ 64; omega)]
    have hafter : WNear.usageAfter ctx (some S') S' = ctx.storageUsage := by
      simp only [WNear.usageAfter, WNear.storageOf]
      rw [← hraw]
      omega
    have hdef : deficit ctx S' =
        stakeDeficit ctx.protocol e.context.storageUsage.toNat e.context.accountBalance ctx.locked := by
      rw [deficit, hafter, hsuN, hbal]
    erw [hstep]
    split
    · rename_i hpos
      refine ⟨by rw [← hdef]; exact hpos, by rw [← hdef]; rfl, ?_⟩
      show [] = logsOf e
      simp [logsOf, hlogs]
    · rename_i hpos
      refine ⟨by rw [← hdef]; exact Nat.eq_zero_of_not_pos hpos, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
      · show returnOf e = .value (WNear.jsonU128 0).toUTF8.toList
        have hd : e.returnData = some [34, 48, 34] := by obtain ⟨_, _, _, _, _, rfl⟩ := hp; rfl
        have hz : (WNear.jsonU128 0).toUTF8.toList = [34, 48, 34] := by decide +kernel
        rw [returnOf, hd, hz]
      · show (finalStorage e).toFinset = encode S'
        rw [hfin, finalStorage_hostOf ctx raw hwf.raw_keys_unique, hraw]
      · exact hbal
      · show e.context.storageUsage.toNat = _ - _ + storageUsageOf ctx.protocol (encode S')
        rw [hsuN, ← hraw]
        omega
      · show logsOf e = []
        simp [logsOf, hlogs]


open NearInterface ContractModel in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem array_absent_refines_v86 (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (modelSt : Option WNear.State)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat)
    (tr : Near.TrieOverlay.State) (bud : Nat) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hlen : bs.length < 2 ^ 24) (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))

    (hentry : CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
    (hrep : (WNear.wnear cfg).Represents raw modelSt) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact array_absent_refines_with_obligations cfg size codeOf raw modelSt ctx S a bs rest j k tr bud
    hp hwf hm hc hsize hlen ho hj hq he hk hend hmodel  hentry
    (copied_agreement_of_represents cfg ctx raw modelSt S a tr hrep hwf hentry.2.value hentry.2.absent _ rfl)
    (copied_agreement_of_represents cfg ctx raw modelSt S a tr hrep hwf hentry.2.value hentry.2.absent _ rfl)

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The existing copied-only contract, preserved as a checked specialization. -/
theorem copied_array_absent_refines_v86 (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (modelSt : Option WNear.State)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat)
    (tr : Near.TrieOverlay.State) (bud : Nat) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hlen : bs.length < 2 ^ 24) (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hentry : CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
    (hrep : (WNear.wnear cfg).Represents raw modelSt) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact array_absent_refines_v86 cfg size codeOf raw modelSt ctx S a bs rest j k tr bud hp hwf hm hc hsize hlen ho hj hq he hk hend hmodel hentry hrep
end WNear.Binary.BalanceOf297AbsentCall
