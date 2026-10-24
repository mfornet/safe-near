import NearNode.Primitives.Account

/-!
# Actions

`near-primitives::action` at `=0.37.4`. `Action` is `BaseAction` plus the two
delegate variants; a delegate action holds `BaseAction`s, which is exactly
`NonDelegateAction` (tags 8 and 14 are not in its table and are rejected).
-/

namespace Near.Node

open Borsh

/-- `TransactionNonce`. -/
inductive TransactionNonce where
  | nonce (nonce : Nonce)
  | gasKeyNonce (nonce : Nonce) (index : NonceIndex)
  deriving BEq, Inhabited

instance : Codec TransactionNonce :=
  .enum "TransactionNonce"
    [.variant 0 Nonce .nonce fun
        | .nonce n => some n
        | _ => none,
      .variant 1 (Nonce × NonceIndex) (fun (n, i) => .gasKeyNonce n i) fun
        | .gasKeyNonce n i => some (n, i)
        | _ => none]

/-- `DeployContractAction`. -/
structure DeployContractAction where
  code : ByteArray
  deriving BEq, Inhabited

instance : Codec DeployContractAction :=
  .iso ByteArray .mk DeployContractAction.code

/-- `FunctionCallAction`. -/
structure FunctionCallAction where
  methodName : String
  args : ByteArray
  gas : Gas
  deposit : Balance
  deriving BEq, Inhabited

instance : Codec FunctionCallAction :=
  .iso (String × ByteArray × Gas × Balance) (fun (m, a, g, d) => ⟨m, a, g, d⟩) fun x =>
    (x.methodName, x.args, x.gas, x.deposit)

/-- `TransferAction`. -/
structure TransferAction where
  deposit : Balance
  deriving BEq, Inhabited

instance : Codec TransferAction :=
  .iso Balance .mk TransferAction.deposit

/-- `StakeAction`. -/
structure StakeAction where
  stake : Balance
  publicKey : PublicKey
  deriving BEq, Inhabited

instance : Codec StakeAction :=
  .iso (Balance × PublicKey) (fun (s, k) => ⟨s, k⟩) fun x => (x.stake, x.publicKey)

/-- `AddKeyAction`. -/
structure AddKeyAction where
  publicKey : PublicKey
  accessKey : AccessKey
  deriving BEq, Inhabited

instance : Codec AddKeyAction :=
  .iso (PublicKey × AccessKey) (fun (k, a) => ⟨k, a⟩) fun x => (x.publicKey, x.accessKey)

/-- `DeleteKeyAction`. -/
structure DeleteKeyAction where
  publicKey : PublicKey
  deriving BEq, Inhabited

instance : Codec DeleteKeyAction :=
  .iso PublicKey .mk DeleteKeyAction.publicKey

/-- `DeleteAccountAction`. -/
structure DeleteAccountAction where
  beneficiaryId : AccountId
  deriving BEq, Inhabited

instance : Codec DeleteAccountAction :=
  .iso AccountId .mk DeleteAccountAction.beneficiaryId

/-- `GlobalContractDeployMode`. -/
inductive GlobalContractDeployMode where
  | codeHash
  | accountId
  deriving BEq, Inhabited

instance : Codec GlobalContractDeployMode :=
  .enum "GlobalContractDeployMode" [.const 0 .codeHash, .const 1 .accountId]

/-- `DeployGlobalContractAction`. -/
structure DeployGlobalContractAction where
  code : ByteArray
  deployMode : GlobalContractDeployMode
  deriving BEq, Inhabited

instance : Codec DeployGlobalContractAction :=
  .iso (ByteArray × GlobalContractDeployMode) (fun (c, m) => ⟨c, m⟩) fun x => (x.code, x.deployMode)

/-- `UseGlobalContractAction`. -/
structure UseGlobalContractAction where
  contractIdentifier : GlobalContractIdentifier
  deriving BEq, Inhabited

instance : Codec UseGlobalContractAction :=
  .iso GlobalContractIdentifier .mk UseGlobalContractAction.contractIdentifier

/-- `DeterministicStateInitAction`. -/
structure DeterministicStateInitAction where
  stateInit : DeterministicAccountStateInit
  deposit : Balance
  deriving BEq, Inhabited

instance : Codec DeterministicStateInitAction :=
  .iso (DeterministicAccountStateInit × Balance) (fun (s, d) => ⟨s, d⟩) fun x =>
    (x.stateInit, x.deposit)

/-- `TransferToGasKeyAction`. -/
structure TransferToGasKeyAction where
  publicKey : PublicKey
  deposit : Balance
  deriving BEq, Inhabited

instance : Codec TransferToGasKeyAction :=
  .iso (PublicKey × Balance) (fun (k, d) => ⟨k, d⟩) fun x => (x.publicKey, x.deposit)

/-- `WithdrawFromGasKeyAction`. -/
structure WithdrawFromGasKeyAction where
  publicKey : PublicKey
  amount : Balance
  deriving BEq, Inhabited

instance : Codec WithdrawFromGasKeyAction :=
  .iso (PublicKey × Balance) (fun (k, a) => ⟨k, a⟩) fun x => (x.publicKey, x.amount)

/-- The actions other than `Delegate` and `DelegateV2` (`NonDelegateAction`). -/
inductive BaseAction where
  | createAccount
  | deployContract (a : DeployContractAction)
  | functionCall (a : FunctionCallAction)
  | transfer (a : TransferAction)
  | stake (a : StakeAction)
  | addKey (a : AddKeyAction)
  | deleteKey (a : DeleteKeyAction)
  | deleteAccount (a : DeleteAccountAction)
  | deployGlobalContract (a : DeployGlobalContractAction)
  | useGlobalContract (a : UseGlobalContractAction)
  | deterministicStateInit (a : DeterministicStateInitAction)
  | transferToGasKey (a : TransferToGasKeyAction)
  | withdrawFromGasKey (a : WithdrawFromGasKeyAction)
  deriving BEq, Inhabited

/-- The variants of `BaseAction`, with the tags they have in `Action`. -/
def baseActionCases : List (Codec.Case BaseAction) :=
  [.const 0 .createAccount,
    .variant 1 DeployContractAction .deployContract fun
      | .deployContract a => some a
      | _ => none,
    .variant 2 FunctionCallAction .functionCall fun
      | .functionCall a => some a
      | _ => none,
    .variant 3 TransferAction .transfer fun
      | .transfer a => some a
      | _ => none,
    .variant 4 StakeAction .stake fun
      | .stake a => some a
      | _ => none,
    .variant 5 AddKeyAction .addKey fun
      | .addKey a => some a
      | _ => none,
    .variant 6 DeleteKeyAction .deleteKey fun
      | .deleteKey a => some a
      | _ => none,
    .variant 7 DeleteAccountAction .deleteAccount fun
      | .deleteAccount a => some a
      | _ => none,
    .variant 9 DeployGlobalContractAction .deployGlobalContract fun
      | .deployGlobalContract a => some a
      | _ => none,
    .variant 10 UseGlobalContractAction .useGlobalContract fun
      | .useGlobalContract a => some a
      | _ => none,
    .variant 11 DeterministicStateInitAction .deterministicStateInit fun
      | .deterministicStateInit a => some a
      | _ => none,
    .variant 12 TransferToGasKeyAction .transferToGasKey fun
      | .transferToGasKey a => some a
      | _ => none,
    .variant 13 WithdrawFromGasKeyAction .withdrawFromGasKey fun
      | .withdrawFromGasKey a => some a
      | _ => none]

instance : Codec BaseAction :=
  .enum "NonDelegateAction" baseActionCases

/-- `DelegateAction`. -/
structure DelegateAction where
  senderId : AccountId
  receiverId : AccountId
  actions : Array BaseAction
  nonce : Nonce
  maxBlockHeight : BlockHeight
  publicKey : PublicKey
  deriving BEq, Inhabited

instance : Codec DelegateAction :=
  .iso (AccountId × AccountId × Array BaseAction × Nonce × BlockHeight × PublicKey)
    (fun (s, r, a, n, h, k) => ⟨s, r, a, n, h, k⟩) fun x =>
    (x.senderId, x.receiverId, x.actions, x.nonce, x.maxBlockHeight, x.publicKey)

/-- The NEP-461 message hash that a delegate action is signed under: SHA-256 of the message
discriminant (`2^30 + 366`, as the `u32` `0x4000016E`) followed by the Borsh encoding of the action. -/
def DelegateAction.signingHash (d : DelegateAction) : CryptoHash :=
  .hash (Codec.encode (0x4000016E : UInt32) ++ Codec.encode d)

/-- `SignedDelegateAction`. -/
structure SignedDelegateAction where
  delegateAction : DelegateAction
  signature : Signature
  deriving BEq, Inhabited

instance : Codec SignedDelegateAction :=
  .iso (DelegateAction × Signature) (fun (d, s) => ⟨d, s⟩) fun x => (x.delegateAction, x.signature)

/-- `DelegateActionV2`: the nonce may carry a gas key index. -/
structure DelegateActionV2 where
  senderId : AccountId
  receiverId : AccountId
  actions : Array BaseAction
  nonce : TransactionNonce
  maxBlockHeight : BlockHeight
  publicKey : PublicKey
  deriving BEq, Inhabited

instance : Codec DelegateActionV2 :=
  .iso (AccountId × AccountId × Array BaseAction × TransactionNonce × BlockHeight × PublicKey)
    (fun (s, r, a, n, h, k) => ⟨s, r, a, n, h, k⟩) fun x =>
    (x.senderId, x.receiverId, x.actions, x.nonce, x.maxBlockHeight, x.publicKey)

/-- `VersionedDelegateActionPayload`. -/
inductive VersionedDelegateActionPayload where
  | v2 (a : DelegateActionV2)
  deriving BEq, Inhabited

instance : Codec VersionedDelegateActionPayload :=
  .enum "VersionedDelegateActionPayload"
    [.variant 0 DelegateActionV2 .v2 fun
        | .v2 a => some a]

/-- The NEP-461 message hash of a versioned payload: the discriminant is `2^30 + 611`, `0x40000263`. -/
def VersionedDelegateActionPayload.signingHash (p : VersionedDelegateActionPayload) : CryptoHash :=
  .hash (Codec.encode (0x40000263 : UInt32) ++ Codec.encode p)

/-- `VersionedSignedDelegateAction`. -/
structure VersionedSignedDelegateAction where
  delegateAction : VersionedDelegateActionPayload
  signature : Signature
  deriving BEq, Inhabited

instance : Codec VersionedSignedDelegateAction :=
  .iso (VersionedDelegateActionPayload × Signature) (fun (d, s) => ⟨d, s⟩) fun x =>
    (x.delegateAction, x.signature)

/-- `Action`. -/
inductive Action where
  | base (a : BaseAction)
  | delegate (a : SignedDelegateAction)
  | delegateV2 (a : VersionedSignedDelegateAction)
  deriving BEq, Inhabited

instance : Codec Action :=
  .enum "Action" <|
    baseActionCases.map
        (·.lift .base fun
          | .base a => some a
          | _ => none) ++
      [.variant 8 SignedDelegateAction .delegate fun
          | .delegate a => some a
          | _ => none,
        .variant 14 VersionedSignedDelegateAction .delegateV2 fun
          | .delegateV2 a => some a
          | _ => none]

end Near.Node
