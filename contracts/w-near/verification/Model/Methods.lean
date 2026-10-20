import Model.Calls

/-!
# The methods

One Lean function per exported method, mirroring the Rust source of
`contracts/w-near/source/w-near` and of the near-contract-standards 3.1.0
`FungibleToken` it delegates to. `step` is the entry point: it adds the checks
the `#[near_bindgen]` wrapper generates (deposit, private, initialisation)
and dispatches.

Every `require` is one panic site in the source, in source order. Panics roll
back the whole execution, so the order only matters for *which* panic is
reported.
-/

namespace WNear

/-- Executions either panic or produce an outcome. -/
abbrev M := Except Panic

/-- `assert!(c, msg)` / `if !c { env::panic(msg) }`. -/
def require (c : Prop) [Decidable c] (p : Panic) : M Unit :=
  if c then pure () else throw p

namespace State

/-- `internal_unwrap_balance_of`. -/
def unwrapBalance (s : State) (a : AccountId) : M Nat :=
  if a ∈ s.registered then pure (s.balance a) else throw (.notRegistered a)

/-- `internal_deposit`: checked additions to the balance and the supply. -/
def deposit (s : State) (a : AccountId) (amount : Nat) : M State := do
  let b ← s.unwrapBalance a
  require (b + amount < u128Bound) .balanceOverflow
  require (s.totalSupply + amount < u128Bound) .totalSupplyOverflow
  pure { s.setBalance a (b + amount) with totalSupply := s.totalSupply + amount }

/-- `internal_withdraw`: checked subtractions from the balance and the supply. -/
def withdraw (s : State) (a : AccountId) (amount : Nat) : M State := do
  let b ← s.unwrapBalance a
  require (amount ≤ b) .notEnoughBalance
  require (amount ≤ s.totalSupply) .totalSupplyOverflow
  pure { s.setBalance a (b - amount) with totalSupply := s.totalSupply - amount }

/-- `internal_register_account`. -/
def registerAccount (s : State) (a : AccountId) : M State := do
  require (a ∉ s.registered) .alreadyRegistered
  pure (s.register a)

/-- `internal_transfer`. Returns the new state and the logs. -/
def transfer (s : State) (sender receiver : AccountId) (amount : Nat) (memo : Option String) :
    M (State × List String) := do
  require (sender ≠ receiver) .sameSenderReceiver
  require (0 < amount) .amountNotPositive
  let s ← s.withdraw sender amount
  let s ← s.deposit receiver amount
  let memoLog := match memo with
    | some m => [s!"Memo: {m}"]
    | none => []
  pure (s, s!"Transfer {amount} from {sender} to {receiver}" :: memoLog)

/-- `storage_balance_bounds()`. -/
def storageBalanceBounds (s : State) : StorageBalanceBounds :=
  { min := s.storageMin, max := some s.storageMin }

/-- `internal_storage_balance_of`. -/
def storageBalanceOf (s : State) (a : AccountId) : Option StorageBalance :=
  if a ∈ s.registered then some { total := s.storageMin, available := 0 } else none

end State

/-- `GAS_FOR_RESOLVE_TRANSFER`. -/
def gasForResolveTransfer : Nat := 5 * 10 ^ 12
/-- `GAS_FOR_FT_TRANSFER_CALL`. -/
def gasForFtTransferCall : Nat := 25 * 10 ^ 12 + gasForResolveTransfer

/-- `FungibleTokenMetadata` returned by `ft_metadata`. -/
def metadata : Metadata :=
  { spec := "ft-1.0.0", name := "Wrapped NEAR fungible token", symbol := "wNEAR",
    icon := none, reference := none, referenceHash := none, decimals := 24 }

/-- `new()`: empty token whose per-account storage cost was measured with a
64-byte account id. -/
@[blueprint "def:new"
  (statement := /-- \texttt{new}: the empty state (no accounts, supply $0$) with $\mathit{accountStorageUsage}$ set to the bytes of one entry for a 64-byte account id. -/)]
def new (cfg : Config) : Outcome :=
  { state := { registered := ∅, balance := fun _ => 0, totalSupply := 0,
               accountStorageUsage := cfg.measuredAccountStorageUsage } }

/-- `near_deposit()`: mint the attached deposit to the predecessor, registering
it first (and keeping the registration fee) if needed. -/
@[blueprint "def:near-deposit"
  (statement := /-- \texttt{near\_deposit}: requires a positive attached deposit $d$. If the predecessor is not registered, requires $d \ge \mathrm{storageMin}$, registers it and sets $d := d - \mathrm{storageMin}$. Then adds $d$ to the predecessor's balance and to the total supply, panicking on \texttt{u128} overflow. -/)]
def nearDeposit (s : State) (env : Env) : M Outcome := do
  let amount := env.attachedDeposit
  require (0 < amount) .requiresPositiveDeposit
  let a := env.predecessor
  let (s, amount) ←
    if a ∈ s.registered then pure (s, amount)
    else do
      require (s.storageMin ≤ amount) .depositTooSmall
      let s ← s.registerAccount a
      pure (s, amount - s.storageMin)
  let s ← s.deposit a amount
  pure { state := s, logs := [s!"Deposit {amount} NEAR to {a}"] }

/-- `near_withdraw(amount)`: burn from the predecessor, schedule a transfer of
that amount plus the attached yoctoNEAR, and delegate the call's result to the
payout receipt. This local success does not assert eventual payout success. -/
@[blueprint "def:near-withdraw"
  (statement := /-- \texttt{near\_withdraw}$(a)$: requires exactly 1 yoctoNEAR attached and a registered predecessor with balance at least $a$; subtracts $a$ from its balance and from the total supply and schedules a transfer of $a + 1$ yoctoNEAR to it, returning that transfer receipt's result (local index 0). -/)]
def nearWithdraw (s : State) (env : Env) (amount : Nat) : M Outcome := do
  require (env.attachedDeposit = 1) .requiresOneYocto
  let a := env.predecessor
  let s ← s.withdraw a amount
  require (amount + 1 < u128Bound) .arithmeticOverflow
  pure { state := s, promises := [.transfer a (amount + 1)], ret := .promise 0,
         logs := [s!"Withdraw {amount} NEAR from {a}"] }

/-- `ft_transfer(receiver_id, amount, memo)`. -/
@[blueprint "def:ft-transfer"
  (statement := /-- \texttt{ft\_transfer}$(r, a, \mathit{memo})$: requires 1 yoctoNEAR, $r \ne$ predecessor and $a > 0$; moves $a$ from the predecessor to $r$, both of which must be registered. -/)]
def ftTransfer (s : State) (env : Env) (receiver : AccountId) (amount : Nat)
    (memo : Option String) : M Outcome := do
  require (env.attachedDeposit = 1) .requiresOneYocto
  let (s, logs) ← s.transfer env.predecessor receiver amount memo
  pure { state := s, logs }

/-- `ft_transfer_call(receiver_id, amount, memo, msg)`: transfer, then call
`ft_on_transfer` on the receiver with the remaining gas, then resolve on self. -/
@[blueprint "def:ft-transfer-call"
  (statement := /-- \texttt{ft\_transfer\_call}$(r, a, \mathit{memo}, \mathit{msg})$: as \cref{def:ft-transfer}, then creates the promise \texttt{ft\_on\_transfer} on $r$ with all the prepaid gas but 30 TGas (panicking if there is less), followed by the callback \texttt{ft\_resolve\_transfer} on the contract itself with 5 TGas; the call's result is that of the callback. -/)]
def ftTransferCall (s : State) (env : Env) (receiver : AccountId) (amount : Nat)
    (memo : Option String) (msg : String) : M Outcome := do
  require (env.attachedDeposit = 1) .requiresOneYocto
  let sender := env.predecessor
  let (s, logs) ← s.transfer sender receiver amount memo
  require (gasForFtTransferCall ≤ env.prepaidGas) .arithmeticOverflow
  let onTransfer : Promise :=
    .call receiver (.ftOnTransfer sender amount msg) 0 (env.prepaidGas - gasForFtTransferCall)
  let resolve : Promise :=
    .call env.currentAccount (.ftResolveTransfer sender receiver amount) 0 gasForResolveTransfer
  pure { state := s, promises := [.then onTransfer resolve], ret := .promise 1, logs }

/-- The unused amount reported by `ft_on_transfer`: everything if the call
failed or its return value did not parse, else the returned value capped by
`amount`. -/
def unusedAmount (amount : Nat) : PromiseResult → M Nat
  | .notReady => throw .promiseNotReady
  | .failed => pure amount
  | .successful none => pure amount
  | .successful (some u) => pure (min amount u)

/-- The refund part of `internal_ft_resolve_transfer`, once the unused amount
is known: move `min(unused, balance(receiver))` back to the sender, or burn it
if the sender has unregistered meanwhile. Returns the used amount. -/
def resolveRefund (s : State) (sender receiver : AccountId) (amount unused : Nat) : M Outcome :=
  if 0 < unused then
    let receiverBalance := s.balanceOf receiver
    if 0 < receiverBalance then
      let refund := min receiverBalance unused
      let s := s.setBalance receiver (receiverBalance - refund)
      if sender ∈ s.registered then do
        require (s.balance sender + refund < u128Bound) .arithmeticOverflow
        pure { state := s.setBalance sender (s.balance sender + refund),
               ret := .u128 (amount - refund),
               logs := [s!"Refund {refund} from {receiver} to {sender}"] }
      else do
        require (refund ≤ s.totalSupply) .arithmeticOverflow
        pure { state := { s with totalSupply := s.totalSupply - refund }, ret := .u128 amount,
               logs := ["The account of the sender was deleted"] }
    else pure { state := s, ret := .u128 amount }
  else pure { state := s, ret := .u128 amount }

/-- `ft_resolve_transfer(sender_id, receiver_id, amount)`: read the result of
`ft_on_transfer`, then refund the unused part of the transfer to the sender,
capped by what the receiver still holds; burn it instead if the sender has
unregistered meanwhile. Returns the used amount. -/
@[blueprint "def:ft-resolve-transfer"
  (statement := /-- \texttt{ft\_resolve\_transfer}$(s, r, a)$: let $u$ be the unused amount, $a$ if the awaited call failed or its return value did not parse, else $\min(a, \text{returned})$. Move $\min(u, \mathit{balance}(r))$ from $r$ to $s$; if $s$ is no longer registered, burn it from the total supply instead. Returns the used amount, $a$ minus the refund (or $a$ when burning). -/)]
def ftResolveTransfer (s : State) (env : Env) (sender receiver : AccountId)
    (amount : Nat) : M Outcome := do
  let result ← match env.promiseResult with
    | some r => pure r
    | none => throw .noPromiseResult
  let unused ← unusedAmount amount result
  resolveRefund s sender receiver amount unused

/-- `storage_deposit(account_id, registration_only)`: register `account_id`
(default: the predecessor) keeping the fee, refund the rest to the predecessor. -/
@[blueprint "def:storage-deposit"
  (statement := /-- \texttt{storage\_deposit}$(\mathit{account}, \_)$: for the given account (default: the predecessor), if it is already registered refund the whole deposit to the predecessor; otherwise require deposit $\ge \mathrm{storageMin}$, register it and refund the excess to the predecessor. -/)]
def storageDeposit (s : State) (env : Env) (account : Option AccountId)
    (_registrationOnly : Option Bool) : M Outcome := do
  let amount := env.attachedDeposit
  let a := account.getD env.predecessor
  if a ∈ s.registered then
    pure { state := s,
           promises := if 0 < amount then [.transfer env.predecessor amount] else [],
           ret := .storageBalance { total := s.storageMin, available := 0 },
           logs := ["The account is already registered, refunding the deposit"] }
  else
    require (s.storageMin ≤ amount) .storageDepositTooSmall
    let s ← s.registerAccount a
    let refund := amount - s.storageMin
    pure { state := s,
           promises := if 0 < refund then [.transfer env.predecessor refund] else [],
           ret := .storageBalance { total := s.storageMin, available := 0 } }

/-- `storage_withdraw(amount)`: nothing is ever available, so only `amount = 0`
or no amount succeeds. -/
@[blueprint "def:storage-withdraw"
  (statement := /-- \texttt{storage\_withdraw}$(a)$: requires 1 yoctoNEAR and a registered predecessor; panics if $a > 0$ (nothing is ever withdrawable); changes nothing. -/)]
def storageWithdraw (s : State) (env : Env) (amount : Option Nat) : M Outcome := do
  require (env.attachedDeposit = 1) .requiresOneYocto
  let a := env.predecessor
  require (a ∈ s.registered) (.notRegistered a)
  match amount with
  | some n => require (n = 0) .storageWithdrawPositive
  | none => pure ()
  pure { state := s, ret := .storageBalance { total := s.storageMin, available := 0 } }

/-- `storage_unregister(force)`: remove the predecessor, burning its balance
(only allowed with `force` when positive), and refund the fee plus 1 yoctoNEAR. -/
@[blueprint "def:storage-unregister"
  (statement := /-- \texttt{storage\_unregister}$(\mathit{force})$: requires 1 yoctoNEAR. If the predecessor is registered, requires its balance to be $0$ or $\mathit{force}$; removes it, subtracts its balance from the total supply and transfers $\mathrm{storageMin} + 1$ yoctoNEAR back to it. Otherwise returns \texttt{false}. -/)]
def storageUnregister (s : State) (env : Env) (force : Option Bool) : M Outcome := do
  require (env.attachedDeposit = 1) .requiresOneYocto
  let a := env.predecessor
  let force := force.getD false
  if a ∈ s.registered then
    let b := s.balance a
    require (b = 0 ∨ force = true) .unregisterWithBalance
    require (b ≤ s.totalSupply) .arithmeticOverflow
    pure { state := { s.unregister a with totalSupply := s.totalSupply - b },
           promises := [.transfer a (s.storageMin + 1)], ret := .bool true }
  else
    pure { state := s, ret := .bool false, logs := [s!"The account {a} is not registered"] }

/-- Dispatch on an initialised contract (everything but `new`). -/
def dispatch (s : State) (env : Env) : Call → M Outcome
  | .new => throw .alreadyInitialized
  | .nearDeposit => nearDeposit s env
  | .nearWithdraw amount => nearWithdraw s env amount
  | .ftTransfer receiver amount memo => ftTransfer s env receiver amount memo
  | .ftTransferCall receiver amount memo msg => ftTransferCall s env receiver amount memo msg
  | .ftResolveTransfer sender receiver amount => ftResolveTransfer s env sender receiver amount
  | .ftTotalSupply => pure { state := s, ret := .u128 s.totalSupply }
  | .ftBalanceOf a => pure { state := s, ret := .u128 (s.balanceOf a) }
  | .ftMetadata => pure { state := s, ret := .metadata metadata }
  | .storageDeposit account registrationOnly => storageDeposit s env account registrationOnly
  | .storageWithdraw amount => storageWithdraw s env amount
  | .storageUnregister force => storageUnregister s env force
  | .storageBalanceBounds => pure { state := s, ret := .storageBalanceBounds s.storageBalanceBounds }
  | .storageBalanceOf a => pure { state := s, ret := .optStorageBalance (s.storageBalanceOf a) }
  | .storageMinimumBalance => pure { state := s, ret := .u128 s.storageMin }

/-- One execution of the contract. `st = none` is an account whose contract
state (`STATE` key) does not exist yet. The prologue is what
`#[near_bindgen]` generates around every method (near-sdk-core 3.1.0):
deposit check for non-payable, non-view methods; predecessor check for
`#[private]` methods; `state_exists` check for `#[init]`; `PanicOnDefault`
for everything else. -/
@[blueprint "def:step"
  (statement := /-- One execution of the contract on an optional state (absent before \texttt{new}): panic if a non-payable mutating method received a deposit, if a private method was not called by the contract itself, if \texttt{new} finds a state or any other method finds none; otherwise run the method. -/)]
def step (cfg : Config) (st : Option State) (env : Env) (call : Call) : M Outcome := do
  if !call.isPayable && !call.isView then
    require (env.attachedDeposit = 0) (.depositNotAccepted call.methodName)
  if call.isPrivate then
    require (env.predecessor = env.currentAccount) (.privateMethod call.methodName)
  match call, st with
  | .new, none => pure (new cfg)
  | .new, some _ => throw .alreadyInitialized
  | _, none => throw .notInitialized
  | c, some s => dispatch s env c

end WNear
