import Proofs.Economics

/-! Kernel-checked source-model witnesses. These are not evidence that these
receipt schedules execute on mainnet: binary and scheduler refinement are open. -/
namespace Linkdrop

def selfEnv : Env := ⟨"near", "near", 1, 0, []⟩

def fundedEnv (n : Nat) : Env := { selfEnv with predecessor := "funder.near", deposit := n }

/-- Deposit 10, start claiming, deposit 7 before resolution, resolve creation.
The callback signer key is inherited from the original claiming transaction. -/
def delayedClaim (success : Bool) : Except Panic (Option Nat × Option Nat × Option Nat × List Receipt) := do
  let initialized ← step empty selfEnv .new
  let funded ← step initialized.state (fundedEnv 10) (.send 1)
  let pending ← step funded.state selfEnv (.createAndClaim "alice.near" 2)
  let toppedUp ← step pending.state (fundedEnv 7) (.send 1)
  let resolved ← step toppedUp.state { selfEnv with results := [if success then .successful [] else .failed] } (.onClaimed 10)
  pure (pending.state.accounts 1, toppedUp.state.accounts 1,
    resolved.state.accounts 1, resolved.receipts)

/-- Failure overwrites the fresh 7 with the old 10, instead of preserving 17. -/
theorem failed_callback_overwrites_topup :
    delayedClaim false = .ok (none, some 7, some 10, []) := by rfl

/-- Success leaves the fresh balance in the map while scheduling deletion of its
claim key. Thus map membership cannot imply that a claim access key exists. -/
theorem successful_callback_deletes_topped_up_key :
    delayedClaim true = .ok (none, some 7, some 7,
      [⟨"near", [.deleteKey 1], none⟩]) := by rfl

/-- A second send still credits the map and requests another AddKey; whether
that request fails because the key exists is not checked by send. -/
theorem repeated_send_requests_key_again :
    (do
      let initialized ← step empty selfEnv .new
      let first ← step initialized.state (fundedEnv 10) (.send 1)
      let second ← step first.state (fundedEnv 7) (.send 1)
      pure (second.state.accounts 1, second.receipts)) =
    .ok (some 17, [⟨"near", [.limitedKey 1 (some keyAllowance) "near"
      "claim,create_account_and_claim"], none⟩]) := by rfl

/-- A successful claim has no resolver to recover a later failed payout. -/
theorem claim_has_no_refund_callback :
    (do
      let initialized ← step empty selfEnv .new
      let funded ← step initialized.state (fundedEnv 10) (.send 1)
      let claimed ← step funded.state selfEnv (.claim "absent.near")
      pure (claimed.state.accounts 1, claimed.receipts, claimed.result)) =
    .ok (none, [⟨"near", [.deleteKey 1], none⟩,
      ⟨"absent.near", [.transfer 10], none⟩], .promise 1) := by rfl

end Linkdrop
