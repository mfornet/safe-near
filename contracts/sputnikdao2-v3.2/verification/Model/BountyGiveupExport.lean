import Model.ExportWrapper
import Model.BountyTrie

namespace SputnikDAO2

/-! Export-level projection of `bounty_giveup`. The refund amount records the
transfer promise scheduled by the source; execution of that promise and
transaction rollback are runtime obligations. The policy value and root codec
are explicit inputs. -/

def giveupStoredClaim (state : BountyStorageState) (account : String)
    (bountyId now forgiveness currentBond : Nat) :
    Option (BountyStorageState × Option Nat) := do
  if now > maxU64 || forgiveness > maxU64 || currentBond > maxU128 then none
  else
    let (removed, claim) ← removeStoredClaim state account bountyId
    if claim.start > maxU64 || now < claim.start then none
    else if now - claim.start > forgiveness then
      some (removed, none)
    else
      some ({ removed with locked := removed.locked - currentBond },
        some currentBond)

def runBountyGiveupExport (raw : BountyRawTrie)
    (ctx : CallWrapperContext) (state : Option BountyStorageState)
    (policy : Option (Nat × Nat)) (bountyId now : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) :
    Option (BountyRawTrie × Option Nat) := do
  let before ← state
  let (forgiveness, currentBond) ← policy
  let (after, refund) ← giveupStoredClaim before ctx.predecessor
    bountyId now forgiveness currentBond
  let afterRaw ← bountyRawRemoveClaim raw before ctx.predecessor bountyId
  let final ← runGeneratedCallWrapper raw "bounty_giveup"
    { ctx with stateDecoded := state.isSome }
    (some (afterRaw, encodeRoot after))
  some (final, refund)

end SputnikDAO2
