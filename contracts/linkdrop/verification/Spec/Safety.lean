import Model

namespace Linkdrop.Spec

/-- Representation invariants for every successful exported model call. -/
def InvPreserved : Prop :=
  ∀ s e c out, s.WF → e.deposit ≤ maxAmount → c.WF →
    step s e c = .ok out → out.state.WF

/-- Private entry points require the predecessor to be this contract. This alone
is NOT a statement that the signer is a legitimate claimant or callback. -/
def PrivateAuthorization : Prop :=
  ∀ s e c out, c.private = true → step s e c = .ok out → e.predecessor = e.current

/-- Only send, claim, create-and-claim and its resolver can change map entries;
all changes are confined to the explicit send key or inherited signer key. -/
def touchedKey (e : Env) : Call → Option Key
  | .send k => some k
  | .claim _ | .createAndClaim .. | .onClaimed _ => some e.signerKey
  | _ => none

def MapAuthorization : Prop :=
  ∀ s e c out k, s.WF → step s e c = .ok out → touchedKey e c ≠ some k →
    out.state.accounts k = s.accounts k

/-- Views may fail for absent keys, but successful views have no effects. -/
def ViewsPure : Prop :=
  ∀ s e c out, c.view = true → step s e c = .ok out →
    out.state = s ∧ out.receipts = []

/-- A successful call never returns a nonexistent local receipt index. -/
def ReturnSelection : Prop :=
  ∀ s e c out i, step s e c = .ok out → out.result = .promise i →
    i < out.receipts.length

/-- Initialization creates an empty map and subsequent initialization fails. -/
def InitOnce : Prop :=
  (∀ s e, s.initialized = true → e.deposit = 0 → step s e .new = .error .initialized) ∧
  (∀ s e out, step s e .new = .ok out →
    out.state.initialized = true ∧ ∀ k, out.state.accounts k = none)

/-- Callbacks reject missing or extra results rather than treating them as failure. -/
def CallbackArity : Prop :=
  ∀ s e c out, (∃ a n, c = .onCreated a n) ∨ (∃ n, c = .onClaimed n) →
    step s e c = .ok out → e.results.length = 1

end Linkdrop.Spec
