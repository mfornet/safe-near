import Bridge.Methods.NearDepositWords
import Bridge.Methods.FtTotalSupplyModel

/-!
# Model agreement for `ft_balance_of`

Connect an arbitrary requested account's encoded storage record and the decoded
`u128` (defaulting to zero when absent) to the model's exact boundary result.
This does not prove execution of the Wasm method or its argument reader.
-/

namespace WNear.Binary.FtBalanceOfMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.NearDepositMethod
open WNear.Binary.FtTotalSupplyMethod

/-- The exact model boundary result, including the storage-stake failure. -/
theorem step_eq (cfg : WNear.Config) (ctx : Context) (s : WNear.State) (a : WNear.AccountId) :
    (WNear.wnear cfg).step ctx (some s) (.ftBalanceOf a) =
      if 0 < deficit ctx s then .error { failure := .lackBalanceForState (deficit ctx s), logs := [] }
      else .ok { state := s, ret := .u128 (s.balanceOf a), logs := [], promises := [] } := by
  rfl

/-- The represented account record is exactly the optional pair of machine words. -/
theorem reg_storage (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (a : WNear.AccountId) :
    h.storage (WNear.accountKey a) = (regOf s a).map
      (fun p => storeBytes (.i64 p.1) 8 ++ storeBytes (.i64 p.2) 8) := by
  rw [accountStorage_of_eraseP ctx raw s hwf hraw a h he]
  unfold regOf
  split
  · simp only [Option.map_some]
    exact congrArg some (DepositBody234.sb_u128 _)
  · rfl

/-- Decoding the words, defaulting to zero, gives the model balance without truncation. -/
theorem reg_value (s : WNear.State) (a : WNear.AccountId) (hs : s.WF) :
    ((regOf s a).map (fun p => p.1.toNat + 2 ^ 64 * p.2.toNat)).getD 0 = s.balanceOf a := by
  unfold regOf WNear.State.balanceOf
  split
  · simp only [Option.map_some, Option.getD_some, balanceWords_val _ (hs.balance_lt a)]
  · rfl

/-- The arbitrary-account lookup and the model boundary result agree, including absent accounts. -/
theorem account_lookup_and_step (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (a : NearInterface.AccountId) :
    ∃ reg : Option (UInt64 × UInt64),
      h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.bytes.length) ++ a.bytes)) =
        reg.map (fun p => storeBytes (.i64 p.1) 8 ++ storeBytes (.i64 p.2) 8) ∧
      (WNear.wnear cfg).step ctx (some s) (.ftBalanceOf (.ofNear a)) =
        if 0 < deficit ctx s then .error { failure := .lackBalanceForState (deficit ctx s), logs := [] }
        else .ok { state := s, ret := .u128 ((reg.map (fun p => p.1.toNat + 2 ^ 64 * p.2.toNat)).getD 0),
                   logs := [], promises := [] } := by
  refine ⟨regOf s (.ofNear a), ?_, ?_⟩
  · rw [← accountKey_ofNear a]
    exact reg_storage ctx raw s hwf hraw h he _
  · rw [reg_value s _ hs]
    exact step_eq cfg ctx s _

end WNear.Binary.FtBalanceOfMethod
