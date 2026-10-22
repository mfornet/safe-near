import Model.State

namespace Linkdrop

def limitedAction (k : LimitedKey) : Action :=
  .limitedKey k.key (if k.allowance = 0 then none else some k.allowance) k.receiver k.methods

def optionActions (o : Options) : List Action :=
  (o.fullKeys.getD []).map Action.fullKey ++
  (o.limitedKeys.getD []).map limitedAction ++
  (o.bytes.toList.map Action.deploy) ++
  (o.base64Bytes.toList.map Action.deploy) ++
  (o.globalHash.toList.map Action.globalHash) ++
  (o.globalAccount.toList.map Action.globalAccount)

def creation (s : State) (e : Env) (account : Account)
    (actions : List Action) (callback : Action) : Outcome :=
  ⟨s, [⟨account, actions, none⟩, ⟨e.current, [callback], some 0⟩], .promise 1⟩

def callbackSuccess (e : Env) : Except Panic Bool :=
  match e.results with
  | [.successful _] => .ok true
  | [.failed] => .ok false
  | [.notReady] => .error .resultNotReady
  | _ => .error .resultCount

/-- Method bodies after SDK entry guards. Receipts represent scheduled actions,
not completed transfers or installed keys. -/
def body (s : State) (e : Env) : Call → Except Panic Outcome
  | .new => .ok ⟨⟨true, fun _ => none⟩, [], .unit⟩
  | .send k =>
    if e.deposit = 0 then .error .zeroDeposit else
    let amount := min ((s.accounts k).getD 0 + e.deposit) maxAmount
    .ok ⟨s.set k (some amount),
      [⟨e.current, [.limitedKey k (some keyAllowance) e.current
        "claim,create_account_and_claim"], none⟩], .promise 0⟩
  | .claim account =>
    match s.accounts e.signerKey with
    | none => .error .missingKey
    | some amount => .ok ⟨s.set e.signerKey none,
        [⟨e.current, [.deleteKey e.signerKey], none⟩, ⟨account, [.transfer amount], none⟩], .promise 1⟩
  | .createAndClaim account key =>
    match s.accounts e.signerKey with
    | none => .error .missingKey
    | some amount => .ok (creation (s.set e.signerKey none) e account
        [.create, .fullKey key, .transfer amount] (.onClaimed amount callbackGas callbackWeight))
  | .createAccount account key =>
    .ok (creation s e account [.create, .fullKey key, .transfer e.deposit]
      (.onCreated e.predecessor e.deposit callbackGas callbackWeight))
  | .createAdvanced account o =>
    if !o.present then .error .noOptions else
    if o.deployments > 1 then .error .conflictingOptions else
    .ok (creation s e account
      ([.create, .transfer e.deposit] ++ optionActions o)
      (.onCreated e.predecessor e.deposit callbackGas callbackWeight))
  | .onCreated predecessor amount =>
    match callbackSuccess e with
    | .error err => .error err
    | .ok success => .ok ⟨s,
        if success then [] else [⟨predecessor, [.transfer amount], none⟩], .boolean success⟩
  | .onClaimed amount =>
    match callbackSuccess e with
    | .error err => .error err
    | .ok success =>
      if success then
        .ok ⟨s, [⟨e.current, [.deleteKey e.signerKey], none⟩], .boolean true⟩
      else
        .ok ⟨s.set e.signerKey (some amount), [], .boolean false⟩
  | .getBalance k =>
    match s.accounts k with
    | none => .error .missingKey
    | some n => .ok ⟨s, [], .balance n⟩
  | .getInformation k =>
    match s.accounts k with
    | none => .error .missingKey
    | some n => .ok ⟨s, [], .information n⟩

/-- SDK 5.17.1 checks privacy, then deposit, then parses arguments, then
initializes/loads state. Parsed-argument validity is a refinement precondition. -/
def step (s : State) (e : Env) (c : Call) : Except Panic Outcome :=
  if c.private ∧ e.predecessor ≠ e.current then .error .privateCall else
  if !c.payable ∧ !c.view ∧ e.deposit ≠ 0 then .error .deposit else
  if c = .new ∧ s.initialized then .error .initialized else
  if c ≠ .new ∧ !s.initialized then .error .uninitialized else
  body s e c

end Linkdrop
