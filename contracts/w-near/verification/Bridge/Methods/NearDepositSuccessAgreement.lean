import Bridge.Methods.NearDepositUsageModel

/-!
# The successful initialized deposit agrees with the model

The final storage, usage, balance, return value and log match the minted model state.
The account's storage-stake check may still reject the call; both boundaries perform
the same check on those same effects.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.DepositBody
open WNear.Binary.NewBody (Keep keep)
open WNear.Binary.FtTotalSupplyMethod (LimitsV86)

theorem text232_length (h : NearState) (reg : Option (UInt64 × UInt64)) (xb : List UInt8)
    (ha : h.context.predecessorAccountId.length ≤ 64) : (text232 h reg xb).length ≤ 120 := by
  cases reg with
  | none => exact (deposit_log_length _ _ _ ha).2
  | some words => exact (deposit_log_length _ _ _ ha).2

/-- The model's successful deposit log passes the protocol's count and byte limits. -/
theorem minted_log_fits (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hok : caseDep h s (regOf s (.ofNear ctx.predecessor)) = .ok)
    (hl : LimitsV86 ctx.protocol) (hn : 1 ≤ ctx.protocol.wasm.limits.maxNumberLogs) :
    logLimitError ctx.protocol (mintedOutcome s (.ofContext ctx)).logs = none := by
  have hp := predecessor_properties_of_eraseP ctx raw h he
  have hb := text232_length h (regOf s (.ofNear ctx.predecessor)) (WNear.Borsh.u64 s.accountStorageUsage) hp.2.1
  rw [text232_model ctx raw s hwf hs h he hok] at hb
  have hlen : (s!"Deposit {amountOf ctx.attached (modelReg s (.ofNear ctx.predecessor)) s.storageMin} NEAR to {WNear.AccountId.ofNear ctx.predecessor}").utf8ByteSize ≤ 120 := by
    simpa only [WNear.Borsh.byteArray_toList_length, String.toUTF8_eq_toByteArray, String.size_toByteArray] using hb
  have ht := hl.totalLog
  change logLimitError ctx.protocol [_] = none
  simp only [logLimitError, logLimitError.go, List.length_nil, Nat.zero_add, WNear.Env.ofContext]
  rw [if_neg (by omega : ¬ctx.protocol.wasm.limits.maxNumberLogs ≤ 0)]
  rw [if_neg (by omega)]

/-- The model's storage-stake deficit after minting. -/
def mintedDeficit (ctx : Context) (s : WNear.State) : Nat :=
  stakeDeficit ctx.protocol (WNear.usageAfter ctx (some s) (mintedOutcome s (.ofContext ctx)).state)
    (ctx.balance + ctx.attached) ctx.locked

theorem step_deposit_ok (cfg : WNear.Config) (ctx : Context) (s : WNear.State)
    (hok : WNear.nearDeposit s (.ofContext ctx) = .ok (mintedOutcome s (.ofContext ctx)))
    (hl : logLimitError ctx.protocol (mintedOutcome s (.ofContext ctx)).logs = none) :
    (WNear.wnear cfg).step ctx (some s) .nearDeposit =
      if 0 < mintedDeficit ctx s then
        .error { failure := .lackBalanceForState (mintedDeficit ctx s), logs := (mintedOutcome s (.ofContext ctx)).logs }
      else .ok { state := (mintedOutcome s (.ofContext ctx)).state, ret := .unit, promises := [], logs := (mintedOutcome s (.ofContext ctx)).logs } := by
  show WNear.contractStep ctx (some s) .nearDeposit = _
  have hs : WNear.step (.ofRuntime ctx.protocol) (some s) (.ofContext ctx) .nearDeposit =
      .ok (mintedOutcome s (.ofContext ctx)) := hok
  rw [WNear.contractStep, hs]
  simp only [WNear.stepLogs, hl]
  rfl

/-- Agreement from the observable effects, including the runtime's final storage-stake check. -/
theorem agrees_minted (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hraw : raw = WNear.encode s) (e : NearState)
    (hok : WNear.nearDeposit s (.ofContext ctx) = .ok (mintedOutcome s (.ofContext ctx)))
    (hl : logLimitError ctx.protocol (mintedOutcome s (.ofContext ctx)).logs = none)
    (hsto : (finalStorage e).toFinset = WNear.encode (mintedOutcome s (.ofContext ctx)).state)
    (hu : e.context.storageUsage.toNat = ctx.storageUsage - storageUsageOf ctx.protocol raw +
      storageUsageOf ctx.protocol (WNear.encode (mintedOutcome s (.ofContext ctx)).state))
    (hb : e.context.accountBalance = ctx.balance + ctx.attached)
    (hlogs : logsOf e = (mintedOutcome s (.ofContext ctx)).logs) (hr : e.returnData = none) :
    AgreesWith (WNear.wnear cfg) ctx raw e ((WNear.wnear cfg).step ctx (some s) .nearDeposit) := by
  have hafter : WNear.usageAfter ctx (some s) (mintedOutcome s (.ofContext ctx)).state =
      e.context.storageUsage.toNat := by
    rw [hu, hraw]
    rfl
  have hdef : mintedDeficit ctx s =
      stakeDeficit ctx.protocol e.context.storageUsage.toNat e.context.accountBalance ctx.locked := by
    rw [mintedDeficit, hafter, hb]
  rw [step_deposit_ok cfg ctx s hok hl]
  split
  · rename_i hpos
    exact ⟨by rw [← hdef]; exact hpos, by rw [← hdef]; rfl, hlogs.symm⟩
  · rename_i hpos
    refine ⟨by rw [← hdef]; exact Nat.eq_zero_of_not_pos hpos, fun _ => rfl, ?_, hsto, hb, hu, hlogs⟩
    show returnOf e = .none
    simp only [returnOf, hr]

/-- Every successful initialized final host satisfies the model agreement obligation. -/
theorem agrees_success_deposit (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (hraw : raw = WNear.encode s) (h h' : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw))
    (hok : caseDep h s (regOf s (.ofNear ctx.predecessor)) = .ok)
    (hl : LimitsV86 ctx.protocol) (hn : 1 ≤ ctx.protocol.wasm.limits.maxNumberLogs)
    (hU : ctx.storageUsage + (85 + ctx.protocol.fees.numExtraBytesRecord) < 2 ^ 64)
    (hp : DepositEffects ctx.protocol.fees.numExtraBytesRecord h s (regOf s (.ofNear ctx.predecessor)) h') :
    AgreesWith (WNear.wnear cfg) ctx raw h' ((WNear.wnear cfg).step ctx (some s) .nearDeposit) := by
  have hm := model_eq_caseDep ctx raw s hwf hs h he
  rw [hok] at hm
  apply agrees_minted cfg ctx raw s hraw h' hm (minted_log_fits ctx raw s hwf hs h he hok hl hn)
    (effects_storage_model ctx raw s hwf hs hraw h h' he hok hp)
    (effects_usage_model ctx raw s hwf hraw h h' he hp hU)
  · exact (congrArg Keep.balance hp.kept).trans
      (eraseP_field he (fun a => a.context.accountBalance) fun _ => rfl)
  · have hlog : h.logs = [] := eraseP_field he NearState.logs fun _ => rfl
    have hlog' : h'.logs = [text232 h (regOf s (.ofNear ctx.predecessor)) (WNear.Borsh.u64 s.accountStorageUsage)] := by
      have hh := congrArg Keep.logs hp.kept
      simpa only [keep, LogStr.logged, hlog, List.nil_append] using hh
    rw [logsOf, hlog', text232_model ctx raw s hwf hs h he hok]
    simp only [List.map_cons, List.map_nil, Wasm.ByteEncoding.byteArray_of_toList,
      Wasm.ByteEncoding.string_fromUTF8_toUTF8, Option.getD_some]
    rfl
  · exact (congrArg Keep.returnData hp.kept).trans (eraseP_field he NearState.returnData fun _ => rfl)

end WNear.Binary.NearDepositMethod
