import NearSdk.Nep141

/-!
# Composing a token's NEP-141 guarantees with a caller's accounting

A contract that takes tokens through `ft_transfer_call` keeps its own record of what each
sender deposited. Whether that record matches the token's balances is a cross-contract
property: it spans the transfer on the token, the caller's `ft_on_transfer`, and the token's
`ft_resolve_transfer`. Here it is derived for a minimal caller, a vault, from the token's
`Nep141.Transfer` and `Nep141.Resolve` alone, with no model of the token's code.
-/

namespace NearSdk.Nep141

variable {α : Type} [DecidableEq α]

/-- A vault's record of what each sender deposited. -/
structure Vault (α : Type) where
  credited : α → Nat

/-- The vault's `ft_on_transfer(sender, amount, msg)`: it keeps `kept` tokens for the sender
and reports `amount - kept` unused. -/
def Vault.onTransfer (vault : Vault α) (sender : α) (kept : Nat) : Vault α :=
  ⟨fun a => if a = sender then vault.credited sender + kept else vault.credited a⟩

/-- `ft_transfer_call(vault, amount)` from `sender`, the vault keeping `kept ≤ amount`, then the
token's resolution, with no other receipt touching the vault's token balance in between. The
vault's token balance rises by exactly what it credited the sender. If the sender still exists,
the sender's balance falls by the same amount and the token reports exactly that as used. If
the sender is gone, the whole amount is reported used and the refund is burnt. -/
theorem transferCall_vault {v₀ v₁ v₂ : View α} {sender vault : α} {amount kept used : Nat}
    (vaultBefore : Vault α)
    (htransfer : Transfer v₀ v₁ sender vault amount) (hkept : kept ≤ amount)
    (hresolve : Resolve v₁ v₂ sender vault amount (amount - kept) used) :
    (vaultBefore.onTransfer sender kept).credited sender = vaultBefore.credited sender + kept ∧
    v₂.balanceOf vault = v₀.balanceOf vault + kept ∧
    ((v₂.balanceOf sender = v₀.balanceOf sender - kept ∧ used = kept) ∨
      (used = amount ∧ v₂.totalSupply = v₀.totalSupply - (amount - kept))) := by
  have hvault₁ := htransfer.receiver_balance
  have hsender₁ := htransfer.sender_balance
  have hsupply₁ := htransfer.totalSupply
  have hrefund : min (amount - kept) (v₁.balanceOf vault) = amount - kept := by
    rw [hvault₁]; omega
  refine ⟨by simp [Vault.onTransfer], ?_⟩
  cases hresolve with
  | refund _ hdistinct heffect hused =>
    rw [hrefund] at heffect hused
    subst heffect
    refine ⟨?_, Or.inl ⟨?_, by omega⟩⟩
    · simp only [View.move, ↓reduceIte, hvault₁]; omega
    · simp only [View.move, Ne.symm hdistinct, ↓reduceIte, hsender₁]
      have := htransfer.covered
      omega
  | burn _ _ heffect hused =>
    rw [hrefund] at heffect
    subst heffect
    refine ⟨?_, Or.inr ⟨hused, ?_⟩⟩
    · simp only [View.burn, ↓reduceIte, hvault₁]; omega
    · simp only [View.burn, hsupply₁]

end NearSdk.Nep141
