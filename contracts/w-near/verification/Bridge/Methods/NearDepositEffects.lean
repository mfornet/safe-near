import Bridge.Methods.NearDepositPre
import Bridge.Methods.NearDepositMintWords

/-!
# Observable host effects of a successful initialized deposit

Flatten the read/mint/write chain in `Post234`. Register updates and trie caches disappear
from the statement; the account record, header, key set, usage and kept fields remain exact.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.DepositBody WNear.Binary.DepositBody234
open WNear.Binary.NewBody (Keep keep)
open Near.TrieOverlay

/-- The header bytes written after minting. -/
def mintedHeader (h : NearState) (s : WNear.State) (reg : Option (UInt64 × UInt64)) : List UInt8 :=
  bytes32 1 ++ WNear.accountsPrefix ++
    StorageBalanceBounds.u128Of ((FtTotalSupply.loOf s).toNat + 2 ^ 64 * (FtTotalSupply.hiOf s).toNat +
      amount232 h reg (WNear.Borsh.u64 s.accountStorageUsage)) ++ WNear.Borsh.u64 s.accountStorageUsage

structure DepositEffects (x : Nat) (h : NearState) (s : WNear.State)
    (reg : Option (UInt64 × UInt64)) (h' : NearState) : Prop where
  storage : ∀ k, h'.storage k =
    if k = StateRead.stateKey then some (mintedHeader h s reg)
    else if k = keyOf h then some (nv232 h reg (WNear.Borsh.u64 s.accountStorageUsage)) else h.storage k
  keys : ∀ k, k ∈ h'.storageKeys ↔ k ∈ h.storageKeys ∨ k = keyOf h ∨ k = StateRead.stateKey
  usage : h'.context.storageUsage = UInt64.ofNat (writeUsage x StateRead.stateKey (mintedHeader h s reg)
    (some (WNear.header s)) (usage232 x h (keyOf h) reg (WNear.Borsh.u64 s.accountStorageUsage)).toNat)
  kept : keep h' = keep (LogStr.logged h (text232 h reg (WNear.Borsh.u64 s.accountStorageUsage)))

/-- The binary postcondition implies the concrete observable read/mint/write effects. -/
theorem post234_effects_of_storage {x : Nat} {h h' : NearState} {s : WNear.State} {st : Near.TrieOverlay.State}
    {reg : Option (UInt64 × UInt64)} (hvalue : h.storage WNear.stateKey = some (WNear.header s))
    (hstore : h.storage (keyOf h) = reg.map (fun p => storeBytes (.i64 p.1) 8 ++ storeBytes (.i64 p.2) 8))
    (hp : Post234 x h st (budDep h) s reg h') : DepositEffects x h s reg h' := by
  obtain ⟨h1, s1, h2, s2, b0, b1, -, -, he1, hp2, -, hb, -, hp3⟩ := hp
  have fields {α : Type} (f : NearState → α) (he : ∀ a, f (erase a) = f a)
      (hr : ∀ a i v, f (a.setRegister i v) = f a)
      (ha : ∀ a t, f { a with storageAccounting := t } = f a) : f h1 = f h :=
    (erase_field he1 f he).trans ((storageReadRegs_field f hr _ _ _).trans (ha _ _))
  have hsto : h1.storage = h.storage := fields _ (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
  have hkeys : h1.storageKeys = h.storageKeys := fields _ (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
  have hkeep : keep h1 = keep h := fields _ (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
  have hdep : h1.context.attachedDeposit = h.context.attachedDeposit :=
    fields (fun a => a.context.attachedDeposit) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
  have hpred : h1.context.predecessorAccountId = h.context.predecessorAccountId :=
    fields (fun a => a.context.predecessorAccountId) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
  have husage : h1.context.storageUsage = h.context.storageUsage :=
    fields (fun a => a.context.storageUsage) (fun _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
  have hid : h1.context.currentAccountId = h.context.currentAccountId := congrArg Keep.id hkeep
  have hstate : h.storage StateRead.stateKey = some (WNear.header s) := by
    rw [StateRead.stateKey_eq]; exact hvalue
  have hamount : amount232 h1 reg (WNear.Borsh.u64 s.accountStorageUsage) =
      amount232 h reg (WNear.Borsh.u64 s.accountStorageUsage) := by
    cases reg <;> simp only [amount232, depOf, EnvGetters.depLo, EnvGetters.depHi, aloOf, ahiOf, hdep]
  have hnv : nv232 h1 reg (WNear.Borsh.u64 s.accountStorageUsage) =
      nv232 h reg (WNear.Borsh.u64 s.accountStorageUsage) := by
    simp only [nv232_amount, hamount]
  have htext : text232 h1 reg (WNear.Borsh.u64 s.accountStorageUsage) =
      text232 h reg (WNear.Borsh.u64 s.accountStorageUsage) := by
    rw [text232_amount, text232_amount, hamount, hpred]
  have huse : usage232 x h1 (keyOf h) reg (WNear.Borsh.u64 s.accountStorageUsage) =
      usage232 x h (keyOf h) reg (WNear.Borsh.u64 s.accountStorageUsage) := by
    cases reg <;> simp only [usage232, hnv, husage]
  have hbud : 4 * lookupProofBound (contractKey h1.context.currentAccountId (keyOf h)) + 48 ≤
      budDep h - readProofCost (contractKey h.context.currentAccountId StateRead.stateKey)
        (h.storage StateRead.stateKey) := by
    rw [hid, hstate]
    simp only [budDep, readProofCost, Option.map_some, Option.getD_some, StateReadModel.header_length]
    omega
  obtain ⟨o1, o2, o3, o4, -⟩ := post232_out hp2 hbud (by rw [hsto]; exact hstore)
  obtain ⟨t, -, -, he3⟩ := hp3
  have hheader : StateWrite.stateBytes 1 WNear.accountsPrefix b0 b1 (WNear.Borsh.u64 s.accountStorageUsage) =
      mintedHeader h s reg := by
    rw [StateWrite.stateBytes, hb, hamount]
    rfl
  have hstate2 : h2.storage StateRead.stateKey = some (WNear.header s) := by
    rw [o1, if_neg (stateKey_ne_key h), hsto, hstate]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    rw [write_storage he3, hheader]
    dsimp only
    rw [o1, hnv, hsto]
  · intro k
    rw [write_keys he3, o2, hkeys, or_assoc]
  · rw [write_usage he3, hheader, hstate2, o3, huse]
  · rw [NewBody.keep_of_erase he3, NewBody.keep_storageWriteHost, o4]
    rw [keep_logged_congr hkeep, htext]

/-- The complete method precondition supplies the two storage facts needed above. -/
theorem post234_effects {x : Nat} {h h' : NearState} {s : WNear.State} {st : Near.TrieOverlay.State}
    {reg : Option (UInt64 × UInt64)} (hpre : DepOk h s st reg)
    (hp : Post234 x h st (budDep h) s reg h') : DepositEffects x h s reg h' :=
  post234_effects_of_storage hpre.value hpre.store hp

/-- The run-level success relation has the same observable effects, including after gas erasure. -/
theorem postDepOk_effects {x : Nat} {h h' : NearState} {s : WNear.State}
    {reg : Option (UInt64 × UInt64)} (hvalue : h.storage WNear.stateKey = some (WNear.header s))
    (hstore : h.storage (keyOf h) = reg.map (fun p => storeBytes (.i64 p.1) 8 ++ storeBytes (.i64 p.2) 8))
    (hp : postDepOk x s reg h h') : DepositEffects x h s reg h' := by
  obtain ⟨st, h3, -, hpost, rfl⟩ := hp
  have hf := post234_effects_of_storage hvalue hstore hpost
  exact ⟨hf.storage, hf.keys, hf.usage, hf.kept⟩

end WNear.Binary.NearDepositMethod
