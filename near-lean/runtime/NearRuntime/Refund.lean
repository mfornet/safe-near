import NearRuntime.State

namespace Near

/-- Best-effort refund to the key currently at this public key. No update is
needed for missing/full/unlimited keys, zero refunds or saturated allowances. -/
def refundAllowanceUpdate (key : AccessKey) (deposit : Nat) : Option AccessKey :=
  match key.permission with
  | .functionCall (some allowance) receiver methods =>
    let restored := min (allowance + deposit) (2 ^ 128 - 1)
    if allowance < restored then
      some { key with permission := .functionCall (some restored) receiver methods }
    else none
  | _ => none

/-- Refund the current finite allowance without recreating a deleted key. -/
def ChainState.refundAllowance (st : ChainState) (id : AccountId) (pk : PublicKey) (deposit : Nat) : ChainState :=
  match st.accessKey? id pk with
  | none => st
  | some key =>
    match refundAllowanceUpdate key deposit with
    | none => st
    | some updated => st.setAccessKey id pk updated

/-- Native `PublicKey::empty(ED25519)` in the byte representation. -/
def emptyPublicKey : PublicKey := 0 :: List.replicate 32 0

/-- A balance refund carries no allowance-restoration marker. -/
def refundReceipt (st : ChainState) (receiver : AccountId) (amount : Nat) : Receipt × ChainState :=
  let (id, st) := st.freshId
  ({ predecessorId := systemAccount, receiverId := receiver, receiptId := id,
     receipt := .action { signerId := systemAccount, signerPublicKey := emptyPublicKey, gasPrice := 0,
                          actions := [.transfer amount] } }, st)

/-- A gas refund preserves the signer key so execution can restore its allowance.
The reference deliberately uses the current key, which may have been replaced. -/
def gasRefundReceipt (st : ChainState) (receiver : AccountId) (pk : PublicKey) (amount : Nat) : Receipt × ChainState :=
  let (id, st) := st.freshId
  ({ predecessorId := systemAccount, receiverId := receiver, receiptId := id,
     receipt := .action { signerId := receiver, signerPublicKey := pk, gasPrice := 0,
                          actions := [.transfer amount] } }, st)

end Near
