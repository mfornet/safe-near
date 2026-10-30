import Bridge.Methods.FtTotalSupplyPre
import Proofs.StorageEncoding

/-!
# The account storage read by initialized `near_deposit`

Connect the initial host's lookup to the account map in the model's exact encoding.
The same fact holds after erasing gas or proof recording, as required by the method bridge.
-/

namespace WNear.Binary

open Wasm Wasm.Near NearLogic NearInterface

/-- If raw storage has no record under a key, the initial host reads `none`. -/
theorem hostOf_storage_none_of_not_mem (ctx : Context) (raw : RawStorage) (key : List UInt8)
    (hn : ∀ value, (key, value) ∉ raw) : (hostOf ctx raw).storage key = none := by
  rw [FtTotalSupplyMethod.hostOf_storage]
  have hf : raw.toList.find? (·.1 == key) = none := List.find?_eq_none.2 fun ⟨k, v⟩ he => by
    simp only [beq_iff_eq]
    intro hk
    subst k
    exact hn v (Finset.mem_toList.1 he)
  rw [hf]
  rfl

namespace NearDepositMethod

/-- The model's Borsh length prefix is the word the binary writes before a key. -/
theorem u32_eq_bytes32 (n : Nat) (hn : n < 2 ^ 32) :
    WNear.Borsh.u32 n = WasmLogic.bytes32 (UInt32.ofNat n) := by
  have hb := ReadRegister.bytes32_of (WNear.Borsh.u32 n) (by simp [NearSdk.Borsh.u32])
  have hd : Memory.decodeLE (WNear.Borsh.u32 n) = n := by
    unfold NearSdk.Borsh.u32
    rw [FtTotalSupply.decodeLE_leBytes, Nat.mod_eq_of_lt]
    simpa only [show 256 ^ 4 = 2 ^ 32 by decide] using hn
  rw [hd] at hb
  exact hb

/-- A context account's model key equals the prefix/length/bytes key used by the Wasm. -/
theorem accountKey_ofNear (a : NearInterface.AccountId) :
    WNear.accountKey (WNear.AccountId.ofNear a) =
      WNear.accountsPrefix ++ (WasmLogic.bytes32 (UInt32.ofNat a.bytes.length) ++ a.bytes) := by
  have ha := a.property
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at ha
  have hn : a.bytes.length < 2 ^ 32 := by
    change a.val.toUTF8.toList.length < 2 ^ 32
    omega
  change WNear.accountsPrefix ++ (WNear.Borsh.u32 a.bytes.length ++ a.bytes) = _
  rw [u32_eq_bytes32 _ hn]

/-- The binary's account lookup sees exactly the model's registered balance. -/
theorem hostOf_account (ctx : Context) (raw : RawStorage) (S : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode S) (a : WNear.AccountId) :
    (hostOf ctx raw).storage (WNear.accountKey a) =
      if a ∈ S.registered then some (WNear.Borsh.u128 (S.balance a)) else none := by
  subst raw
  by_cases ha : a ∈ S.registered
  · rw [if_pos ha]
    exact FtTotalSupplyMethod.hostOf_storage_of_mem hwf (WNear.mem_encode_account.mpr ⟨ha, rfl⟩)
  · rw [if_neg ha]
    apply hostOf_storage_none_of_not_mem
    intro v hv
    exact ha (WNear.mem_encode_account.mp hv).1

/-- Erasing gas and proof recording does not change the represented account record. -/
theorem accountStorage_of_eraseP (ctx : Context) (raw : RawStorage) (S : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode S) (a : WNear.AccountId) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) :
    h.storage (WNear.accountKey a) =
      if a ∈ S.registered then some (WNear.Borsh.u128 (S.balance a)) else none := by
  have hs : h.storage = (hostOf ctx raw).storage := eraseP_field he NearState.storage fun _ => rfl
  rw [hs]
  exact hostOf_account ctx raw S hwf hraw a

/-- The predecessor key that deposit constructs reads the model's account entry, including
when gas and proof recording have been erased for the resource-failure argument. -/
theorem predecessorStorage_of_eraseP (ctx : Context) (raw : RawStorage) (S : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode S) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) :
    h.storage (WNear.accountsPrefix ++
      (WasmLogic.bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)) =
      if WNear.AccountId.ofNear ctx.predecessor ∈ S.registered then
        some (WNear.Borsh.u128 (S.balance (WNear.AccountId.ofNear ctx.predecessor))) else none := by
  have hp : h.context.predecessorAccountId = ctx.predecessor.bytes :=
    eraseP_field he (fun x => x.context.predecessorAccountId) fun _ => rfl
  rw [hp, ← accountKey_ofNear]
  exact accountStorage_of_eraseP ctx raw S hwf hraw _ h he

end NearDepositMethod
end WNear.Binary
