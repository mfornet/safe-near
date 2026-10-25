/-!
# NEP-141 fungible tokens, as an environment contract

What a contract may assume about a NEP-141 token it calls, stated on what any
caller can observe of the token: its balances and total supply. A token
contract's own model satisfies these by proof (wNEAR does,
`contracts/w-near/verification/Proofs/Standards.lean`); a contract that calls a token takes them as
assumptions about that account.
-/

namespace NearSdk.Nep141

variable {α : Type} [DecidableEq α]

/-- What callers observe of a token: `ft_balance_of` and `ft_total_supply`. -/
structure View (α : Type) where
  balanceOf : α → Nat
  totalSupply : Nat

/-- `amount` moved from `source` to `target`. -/
def View.move (v : View α) (source target : α) (amount : Nat) : View α :=
  { v with balanceOf := fun a =>
      if a = source then v.balanceOf source - amount
      else if a = target then v.balanceOf target + amount
      else v.balanceOf a }

/-- `amount` burnt from `holder`. -/
def View.burn (v : View α) (holder : α) (amount : Nat) : View α :=
  { balanceOf := fun a => if a = holder then v.balanceOf holder - amount else v.balanceOf a
    totalSupply := v.totalSupply - amount }

/-- A successful `ft_transfer(receiver, amount)` by `sender`, and the transfer that starts
`ft_transfer_call`: the accounts differ, the amount is positive and covered, and exactly
that amount moves. -/
structure Transfer (v v' : View α) (sender receiver : α) (amount : Nat) : Prop where
  distinct : sender ≠ receiver
  positive : 0 < amount
  covered : amount ≤ v.balanceOf sender
  effect : v' = v.move sender receiver amount

/-- A successful `ft_resolve_transfer(sender, receiver, amount)` after `ft_on_transfer`
reported `unused` tokens: the refund is `min(unused, balance(receiver))` with
`unused ≤ amount`. It goes back to the sender, who keeps `used = amount - refund`; if the
sender is gone it is burnt and the whole amount counts as used. -/
inductive Resolve (v v' : View α) (sender receiver : α) (amount unused used : Nat) : Prop where
  | refund (hle : unused ≤ amount) (hdistinct : receiver ≠ sender)
      (heffect : v' = v.move receiver sender (min unused (v.balanceOf receiver)))
      (hused : used = amount - min unused (v.balanceOf receiver))
  | burn (hle : unused ≤ amount) (hsupply : min unused (v.balanceOf receiver) ≤ v.totalSupply)
      (heffect : v' = v.burn receiver (min unused (v.balanceOf receiver))) (hused : used = amount)

/-- A transfer changes no total supply. -/
theorem Transfer.totalSupply {v v' : View α} {sender receiver : α} {amount : Nat}
    (h : Transfer v v' sender receiver amount) : v'.totalSupply = v.totalSupply := by
  rw [h.effect]; rfl

/-- The receiver gains exactly the amount. -/
theorem Transfer.receiver_balance {v v' : View α} {sender receiver : α} {amount : Nat}
    (h : Transfer v v' sender receiver amount) :
    v'.balanceOf receiver = v.balanceOf receiver + amount := by
  rw [h.effect]
  simp [View.move, Ne.symm h.distinct]

/-- The sender loses exactly the amount. -/
theorem Transfer.sender_balance {v v' : View α} {sender receiver : α} {amount : Nat}
    (h : Transfer v v' sender receiver amount) :
    v'.balanceOf sender = v.balanceOf sender - amount := by
  rw [h.effect]
  simp [View.move]

/-- Other accounts are untouched. -/
theorem Transfer.other_balance {v v' : View α} {sender receiver : α} {amount : Nat}
    (h : Transfer v v' sender receiver amount) {a : α} (hs : a ≠ sender) (hr : a ≠ receiver) :
    v'.balanceOf a = v.balanceOf a := by
  rw [h.effect]
  simp [View.move, hs, hr]

/-- The receiver keeps at most what was transferred. -/
theorem Resolve.used_le {v v' : View α} {sender receiver : α} {amount unused used : Nat}
    (h : Resolve v v' sender receiver amount unused used) : used ≤ amount := by
  cases h <;> omega

/-- Resolution never mints. -/
theorem Resolve.totalSupply_le {v v' : View α} {sender receiver : α} {amount unused used : Nat}
    (h : Resolve v v' sender receiver amount unused used) : v'.totalSupply ≤ v.totalSupply := by
  cases h with
  | refund _ _ heffect _ => rw [heffect]; exact Nat.le_refl _
  | burn _ _ heffect _ => rw [heffect]; exact Nat.sub_le _ _

end NearSdk.Nep141
