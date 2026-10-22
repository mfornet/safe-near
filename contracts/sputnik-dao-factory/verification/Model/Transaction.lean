import Model.Types

/-! A free transaction language keeps source reads/writes in order, with atomic
failure at the model boundary. Its generic evaluator permits a single proof of
raw-key uniqueness for every contract method, including malformed-state paths.
Runtime rollback is a separate refinement obligation, not assumed proved here. -/
namespace SputnikFactory

inductive Tx (α : Type) where
  | ret (value : α)
  | fail (panic : Panic)
  | inspect (next : Raw → Tx α)
  | write (key value : Bytes) (next : Tx α)
  | erase (key : Bytes) (next : Tx α)

def Tx.bind (program : Tx α) (next : α → Tx β) : Tx β :=
  match program with
  | .ret value => next value
  | .fail panic => .fail panic
  | .inspect cont => .inspect fun raw => (cont raw).bind next
  | .write key value cont => .write key value (cont.bind next)
  | .erase key cont => .erase key (cont.bind next)

instance : Monad Tx where
  pure := Tx.ret
  bind := Tx.bind

def Tx.run (program : Tx α) (raw : Raw) : Except Panic (α × Raw) :=
  match program with
  | .ret value => .ok (value, raw)
  | .fail panic => .error panic
  | .inspect next => (next raw).run raw
  | .write key value next => next.run (SputnikFactory.write raw key value)
  | .erase key next => next.run (remove raw key)

def load (key : Bytes) : Tx (Option Bytes) := .inspect fun raw => .ret (read raw key)
def save (key value : Bytes) : Tx Unit := .write key value (.ret ())
def erase (key : Bytes) : Tx Unit := .erase key (.ret ())
def snapshot : Tx Raw := .inspect Tx.ret

def require (condition : Bool) (panic : Panic) : Tx Unit :=
  if condition then pure () else .fail panic

def expect (value : Option α) (panic : Panic) : Tx α :=
  match value with | none => .fail panic | some value => pure value

end SputnikFactory
