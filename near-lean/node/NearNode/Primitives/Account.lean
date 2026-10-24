import NearNode.Primitives.Basic

/-!
# Accounts, access keys and global contracts

`near-primitives-core::account`, `global_contract` and
`deterministic_account_id` at `=0.37.4`.
-/

namespace Near.Node

open Borsh

/-- `FunctionCallPermission`. -/
structure FunctionCallPermission where
  allowance : Option Balance
  receiverId : String
  methodNames : Array String
  deriving BEq, Inhabited

instance : Codec FunctionCallPermission :=
  .iso (Option Balance × String × Array String) (fun (a, r, m) => ⟨a, r, m⟩) fun x =>
    (x.allowance, x.receiverId, x.methodNames)

/-- `GasKeyInfo`. -/
structure GasKeyInfo where
  balance : Balance
  numNonces : NonceIndex
  deriving BEq, Inhabited

instance : Codec GasKeyInfo :=
  .iso (Balance × NonceIndex) (fun (b, n) => ⟨b, n⟩) fun x => (x.balance, x.numNonces)

/-- `AccessKeyPermission`. -/
inductive AccessKeyPermission where
  | functionCall (p : FunctionCallPermission)
  | fullAccess
  | gasKeyFunctionCall (info : GasKeyInfo) (p : FunctionCallPermission)
  | gasKeyFullAccess (info : GasKeyInfo)
  deriving BEq, Inhabited

instance : Codec AccessKeyPermission :=
  .enum "AccessKeyPermission"
    [.variant 0 FunctionCallPermission .functionCall fun
        | .functionCall p => some p
        | _ => none,
      .const 1 .fullAccess,
      .variant 2 (GasKeyInfo × FunctionCallPermission) (fun (i, p) => .gasKeyFunctionCall i p) fun
        | .gasKeyFunctionCall i p => some (i, p)
        | _ => none,
      .variant 3 GasKeyInfo .gasKeyFullAccess fun
        | .gasKeyFullAccess i => some i
        | _ => none]

/-- `AccessKey`. -/
structure AccessKey where
  nonce : Nonce
  permission : AccessKeyPermission
  deriving BEq, Inhabited

instance : Codec AccessKey :=
  .iso (Nonce × AccessKeyPermission) (fun (n, p) => ⟨n, p⟩) fun x => (x.nonce, x.permission)

/-- `GlobalContractIdentifier`. -/
inductive GlobalContractIdentifier where
  | codeHash (hash : CryptoHash)
  | accountId (id : AccountId)
  deriving BEq, Inhabited

instance : Codec GlobalContractIdentifier :=
  .enum "GlobalContractIdentifier"
    [.variant 0 CryptoHash .codeHash fun
        | .codeHash h => some h
        | _ => none,
      .variant 1 AccountId .accountId fun
        | .accountId a => some a
        | _ => none]

/-- `AccountContract`: positional tags, no explicit discriminants. -/
inductive AccountContract where
  | none
  | local (hash : CryptoHash)
  | global (hash : CryptoHash)
  | globalByAccount (id : AccountId)
  deriving BEq, Inhabited

instance : Codec AccountContract :=
  .enum "AccountContract"
    [.const 0 .none,
      .variant 1 CryptoHash .local fun
        | .local h => some h
        | _ => none,
      .variant 2 CryptoHash .global fun
        | .global h => some h
        | _ => none,
      .variant 3 AccountId .globalByAccount fun
        | .globalByAccount a => some a
        | _ => none]

/-- `Account`. V1 is the four legacy fields; V2 is announced by `u128::MAX` and tag 0. -/
inductive Account where
  | v1 (amount locked : Balance) (codeHash : CryptoHash) (storageUsage : StorageUsage)
  | v2 (amount locked : Balance) (storageUsage : StorageUsage) (contract : AccountContract)
  deriving BEq, Inhabited

instance : Codec Account :=
  let c1 : Codec (Balance × CryptoHash × StorageUsage) := inferInstance
  let c2 : Codec (Balance × Balance × StorageUsage × AccountContract) := inferInstance
  { spec :=
      { enc := fun
          | .v1 a l h s => Spec.u128.enc a ++ c1.spec.enc (l, h, s)
          | .v2 a l s c => Spec.u128.enc U128.max ++ 0 :: c2.spec.enc (a, l, s, c)
        dec := fun bytes => do
          let (first, r) ← Spec.u128.dec bytes
          if first == U128.max then
            let (t, r) ← Spec.u8.dec r
            if t != 0 then
              throw (.tag "BorshVersionedAccount" t.toNat)
            let ((a, l, s, c), r) ← c2.spec.dec r
            pure (.v2 a l s c, r)
          else
            let ((l, h, s), r) ← c1.spec.dec r
            pure (.v1 first l h s, r) }
    impl :=
      { put := fun
          | .v1 a l h s, d => c1.impl.put (l, h, s) (Impl.u128.put a d)
          | .v2 a l s c, d => c2.impl.put (a, l, s, c) ((Impl.u128.put U128.max d).push 0)
        get := fun d p =>
          match Impl.u128.get d p with
          | .ok first q =>
            if first == U128.max then
              match Impl.u8.get d q with
              | .ok 0 q => (c2.impl.get d q).map fun (a, l, s, c) => .v2 a l s c
              | .ok t _ => .err (.tag "BorshVersionedAccount" t.toNat)
              | .err e => .err e
            else (c1.impl.get d q).map fun (l, h, s) => .v1 first l h s
          | .err e => .err e } }

/-- `DeterministicAccountStateInitV1`: a global contract and its initial key-value state. -/
structure StateInitV1 where
  code : GlobalContractIdentifier
  data : Array (ByteArray × ByteArray)
  deriving BEq, Inhabited

instance : Codec StateInitV1 :=
  .isoOf (α := GlobalContractIdentifier × Array (ByteArray × ByteArray))
    (.pair inferInstance (.btreeMap compareBytes inferInstance inferInstance))
    (fun (c, d) => ⟨c, d⟩) fun x => (x.code, x.data)

/-- `DeterministicAccountStateInit`. -/
inductive DeterministicAccountStateInit where
  | v1 (init : StateInitV1)
  deriving BEq, Inhabited

instance : Codec DeterministicAccountStateInit :=
  .enum "DeterministicAccountStateInit"
    [.variant 0 StateInitV1 .v1 fun
        | .v1 i => some i]

end Near.Node
