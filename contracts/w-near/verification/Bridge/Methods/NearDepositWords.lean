import Bridge.Methods.NearDepositCases
import Bridge.Methods.NearDepositRuns
import Bridge.Methods.NearDepositStorage

/-!
# The deposit classifier on the represented host

Decode the predecessor's balance, the supply, the storage minimum and the attached deposit
without truncation. The binary's `caseDep` then classifies the actual model result.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.DepositBody

/-- The two words obtained by deserializing a model balance. -/
def balanceWords (n : Nat) : UInt64 × UInt64 :=
  (UInt64.ofNat (Memory.decodeLE ((WNear.Borsh.u128 n).take 8)),
    UInt64.ofNat (Memory.decodeLE ((WNear.Borsh.u128 n).drop 8)))

/-- The optional balance record passed to the binary method contract. -/
def regOf (s : WNear.State) (a : WNear.AccountId) : Option (UInt64 × UInt64) :=
  if a ∈ s.registered then some (balanceWords (s.balance a)) else none

theorem balanceWords_val (n : Nat) (hn : n < 2 ^ 128) :
    (balanceWords n).1.toNat + 2 ^ 64 * (balanceWords n).2.toNat = n := by
  exact (FtTotalSupply.val_u128 n).trans (Nat.mod_eq_of_lt hn)

/-- No balance is truncated when the represented state is well formed. -/
theorem regB_regOf (s : WNear.State) (a : WNear.AccountId) (hs : s.WF) :
    regB (regOf s a) = modelReg s a := by
  unfold regOf modelReg
  split
  · simp only [regB, Option.map_some, balanceWords_val _ (hs.balance_lt a)]
  · rfl

/-- The balance record's bytes are precisely what the represented initial host reads. -/
theorem regOf_storage (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) :
    h.storage (DepositBody234.keyOf h) = (regOf s (.ofNear ctx.predecessor)).map
      (fun p => storeBytes (.i64 p.1) 8 ++ storeBytes (.i64 p.2) 8) := by
  rw [DepositBody234.keyOf, predecessorStorage_of_eraseP ctx raw s hwf hraw h he]
  unfold regOf
  split
  · simp only [Option.map_some]
    exact congrArg some (DepositBody234.sb_u128 _)
  · rfl

/-- The attached deposit is already within the model's `u128` bound. -/
theorem depOf_of_eraseP (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) : depOf h = ctx.attached := by
  have ha : h.context.attachedDeposit = ctx.attached :=
    eraseP_field he (fun x => x.context.attachedDeposit) fun _ => rfl
  have hb : ctx.attached < 2 ^ 128 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) hwf.balance_lt
  exact (EnvGetters.depLo_add_depHi h).trans (by rw [ha, Nat.mod_eq_of_lt hb])

/-- The binary computes the same storage fee as the model's `storageMin`. -/
theorem minOf_model (s : WNear.State) (hs : s.WF) :
    DepositBody.minOf (WNear.Borsh.u64 s.accountStorageUsage) = s.storageMin := by
  have hx : (StorageBalanceBounds.xOf (WNear.Borsh.u64 s.accountStorageUsage)).toNat =
      s.accountStorageUsage % 2 ^ 64 := by
    simp only [StorageBalanceBounds.xOf, WNear.Borsh.u64, FtTotalSupply.decodeLE_leBytes,
      UInt64.toNat_ofNat']
    norm_num
  have hu : s.accountStorageUsage < 2 ^ 64 := hs.usage_lt
  rw [DepositBody.minOf, hx, Nat.mod_eq_of_lt hu]
  rfl

/-- Every input of the binary classifier agrees with the represented model. -/
theorem caseDep_eq_model (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) :
    caseDep h s (regOf s (.ofNear ctx.predecessor)) =
      dcase ctx.attached (modelReg s (.ofNear ctx.predecessor)) s.storageMin s.totalSupply := by
  have ht : (FtTotalSupply.loOf s).toNat + 2 ^ 64 * (FtTotalSupply.hiOf s).toNat = s.totalSupply :=
    (FtTotalSupply.val_loOf s).trans (Nat.mod_eq_of_lt hs.totalSupply_lt)
  rw [caseDep, case232, depOf_of_eraseP ctx raw hwf h he, regB_regOf s _ hs, minOf_model s hs, ht]

/-- The actual initialized binary branch denotes the model's exact result. -/
theorem model_eq_caseDep (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) :
    WNear.nearDeposit s (.ofContext ctx) =
      caseResult (caseDep h s (regOf s (.ofNear ctx.predecessor))) s (.ofContext ctx) := by
  rw [caseDep_eq_model ctx raw s hwf hs h he]
  exact model_eq_dcase s (.ofContext ctx)

end WNear.Binary.NearDepositMethod
