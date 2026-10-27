import NearRuntime.Boundary
import Lean.Data.Json

/-!
# Differential scenarios: a contract model against near-lean, step by step

A scenario is an initial world (the contract account, its contract storage,
other accounts' records in the chunk trie) and a timeline of blocks. Each
block executes an ordered list of receipts on the contract: fresh calls,
deliveries of receipts the contract created earlier (with the promise results
the scenario chooses), and balance changes from outside. Everything the
runtime would decide (which block a receipt lands in, the order inside a
chunk, what a callback's dependencies returned) is written in the scenario,
so both sides run exactly the same inputs.

Every receipt runs on `Near.Boundary.execOn` (the runtime of `refines_*`) and
on the model, and is checked against the three clauses of
`NearInterface.Refines` for that context:

* no execution reports an interpreter limitation;
* for a call: with the model's gas bound attached, `Matches` and used gas
  within the bound; with less, `Matches` or an out-of-gas failure with no
  effects whose logs are a prefix of the model's;
* input that is no call fails with no effects.

The world then advances by the binary's observation. Before each receipt the
runner checks the hypotheses of `Refines`: the contract storage represents
the model state (`encodeState`, the invariant), and the context is one the
runtime builds (`Context.WF`, the parts that can fail here). A violated
hypothesis is a scenario error, not a discrepancy.

Within a block the trie keeps its node cache and committed writes, as in one
chunk; a new block starts from the committed records with a cold cache.

The runner is contract-independent: a contract plugs in an `ExecModel`.
-/

namespace Scenario

open Lean NearInterface Wasm Wasm.Near

abbrev RawBytes := List UInt8

/-! ## Executable models -/

/-- What `ContractModel` states as relations, as functions the runner can run. -/
structure ExecModel where
  State : Type
  Call : Type
  Ret : Type
  Panic : Type
  Promise : Type
  /-- `Parses` as a function (every model's `Parses` is functional). -/
  decode : String → RawBytes → Option Call
  step : Context → Option State → Call → StepResult Panic State Ret Promise
  gas : Context → Option State → Call → Gas
  encodeState : State → RawStorage
  encodeRet : Ret → ReturnData
  encodeReceipts : Gas → List Promise → List RawReceipt
  failure : ModelFailure Panic → Failure
  /-- Why a state breaks the invariant, if it does (the decidable part). -/
  invViolation : State → Option String
  /-- The scenario's `state` field: a model state and the listing of its storage. -/
  initial : Json → Except String (Option State × List (RawBytes × RawBytes))
  callName : Call → String

/-! ## Printing -/

def hex (bs : RawBytes) : String :=
  String.join (bs.map fun b =>
    String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)])

/-- At most `n` characters, with the length when cut. -/
def clip (s : String) (n : Nat := 160) : String :=
  if s.length ≤ n then s else s!"{(s.take n).toString}…({s.length} chars)"

def showLogs (logs : List String) : String := toString (logs.map (clip ·))

/-- Bytes as text when they are printable UTF-8, else hex. -/
def showBytes (bs : RawBytes) : String :=
  match String.fromUTF8? ⟨bs.toArray⟩ with
  | some s => if s.all (fun c => ' ' ≤ c && c ≤ '~') then clip (repr s |>.pretty) else clip ("0x" ++ hex bs)
  | none => clip ("0x" ++ hex bs)

def showReturn : ReturnData → String
  | .value bs => s!"value {showBytes bs}"
  | .receiptIndex i => s!"receipt {i}"
  | .none => "none"

def showOutcome : Except Failure ReturnData → String
  | .ok d => s!"ok ({showReturn d})"
  | .error f => s!"error {repr f |>.pretty}"

def showAction : PromiseAction → String
  | .functionCall m args deposit gas =>
    s!"call {showBytes m}({showBytes args}) deposit {deposit} gas {gas.toNat}"
  | .transfer amount => s!"transfer {amount}"
  | _ => "other action"

def showReceipt (r : RawReceipt) : String :=
  s!"→ {showBytes r.receiverId}: [{", ".intercalate (r.actions.map showAction)}] after {r.dependencies}"

def tgas (g : Nat) : String :=
  let t := g / 10 ^ 9
  s!"{t / 1000}.{toString (t % 1000 + 1000) |>.drop 1} Tgas"

/-! ## Scenario input -/

def field? (j : Json) (k : String) : Option Json :=
  match j.getObjVal? k with
  | .ok Json.null => none
  | .ok v => some v
  | .error _ => none

/-- A natural number written as a JSON number or a decimal string. -/
def natOf (j : Json) : Except String Nat :=
  match j with
  | .str s => match s.toNat? with
    | some n => pure n
    | none => throw s!"not a natural number: {s}"
  | .num _ => match j.getNat? with
    | .ok n => pure n
    | .error e => throw e
  | _ => throw s!"not a natural number: {j.compress}"

def natD (j : Json) (k : String) (d : Nat) : Except String Nat :=
  match field? j k with
  | some v => natOf v
  | none => pure d

def strD (j : Json) (k : String) (d : String) : Except String String :=
  match field? j k with
  | some (.str s) => pure s
  | some v => throw s!"{k}: expected a string, got {v.compress}"
  | none => pure d

def hexDigit (c : Char) : Except String Nat :=
  if c.isDigit then pure (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
  else throw s!"bad hex digit {c}"

def ofHex (s : String) : Except String RawBytes := do
  let rec go : List Char → Except String RawBytes
    | a :: b :: rest => do pure (UInt8.ofNat ((← hexDigit a) * 16 + (← hexDigit b)) :: (← go rest))
    | [] => pure []
    | _ => throw "odd number of hex digits"
  go s.toList

/-- RawBytes: a string is its UTF-8, `{"hex": "..."}` is hex. -/
def bytesOf (j : Json) : Except String RawBytes :=
  match j with
  | .str s => pure s.toUTF8.toList
  | _ => match field? j "hex" with
    | some (.str h) => ofHex h
    | _ => throw s!"not bytes: {j.compress}"

def accountOf (s : String) : Except String AccountId :=
  if h : validAccountIdBytes s.toUTF8.toList = true then pure ⟨s, h⟩
  else throw s!"invalid account id {repr s |>.pretty}"

/-- Text: a string, or a list of parts, each a string or
`{"repeat": s, "times": n}` (for long or deeply nested inputs). -/
def textOf (j : Json) : Except String String :=
  match j with
  | .str s => pure s
  | .arr parts => do
    let ps ← parts.toList.mapM fun p => match p with
      | .str s => pure s
      | p => do
        let s ← match field? p "repeat" with
          | some (.str s) => pure s
          | _ => throw s!"not a text part: {p.compress}"
        let n ← natOf ((field? p "times").getD (.num 1))
        pure (String.join (List.replicate n s))
    pure (String.join ps)
  | _ => throw s!"not text: {j.compress}"

/-- Call arguments: `args` (any JSON value, sent compact), `argsText` (exact
text, see `textOf`) or `argsHex`. Default `{}`. -/
def argsOf (j : Json) : Except String RawBytes := do
  if let some t := field? j "argsText" then return (← textOf t).toUTF8.toList
  if let some (.str h) := field? j "argsHex" then return ← ofHex h
  match field? j "args" with
  | some v => pure v.compress.toUTF8.toList
  | none => pure "{}".toUTF8.toList

/-- Promise results: `{"ok": text}`, `{"okHex": hex}`, `"failed"`, `"notReady"`. -/
def resultOf (j : Json) : Except String PromiseResult :=
  match j with
  | .str "failed" => pure .failed
  | .str "notReady" => pure .notReady
  | _ => match field? j "ok", field? j "okHex" with
    | some t, _ => do pure (.successful (← textOf t).toUTF8.toList)
    | _, some (.str h) => do pure (.successful (← ofHex h))
    | _, _ => throw s!"not a promise result: {j.compress}"

def resultsOf (j : Json) : Except String (Option (List PromiseResult)) :=
  match field? j "results" with
  | none => pure none
  | some v => do
    let arr ← v.getArr?
    pure (some (← arr.toList.mapM resultOf))

/-- How much gas to attach: an amount, or the model's bound shifted by `±n`. -/
inductive GasSpec
  | exact (g : Nat)
  | bound (delta : Int)

def gasSpecOf (j : Json) : Except String GasSpec :=
  match j with
  | .str s =>
    if s == "bound" then pure (.bound 0)
    else if s.startsWith "bound-" then
      match (s.drop 6).toString.toNat? with
      | some n => pure (.bound (-(n : Int)))
      | none => throw s!"bad gas {s}"
    else if s.startsWith "bound+" then
      match (s.drop 6).toString.toNat? with
      | some n => pure (.bound n)
      | none => throw s!"bad gas {s}"
    else (.exact ·) <$> natOf j
  | _ => (.exact ·) <$> natOf j

/-- What a receipt is expected to do. It makes a scenario fail when it no
longer exercises the path it was written for; it is not part of `Refines`. -/
inductive Expect
  | ok | fail | noCall | outOfGas | balanceExceeded | lackBalanceForState | methodNotFound
  | panic (sub : String)
  | other (sub : String)

def expectOf (s : String) : Except String Expect :=
  match s with
  | "ok" => pure .ok
  | "fail" => pure .fail
  | "noCall" => pure .noCall
  | "outOfGas" => pure .outOfGas
  | "balanceExceeded" => pure .balanceExceeded
  | "lackBalanceForState" => pure .lackBalanceForState
  | "methodNotFound" => pure .methodNotFound
  | "panic" => pure (.panic "")
  | "other" => pure (.other "")
  | _ =>
    if s.startsWith "panic:" then pure (.panic (s.drop 6).toString)
    else if s.startsWith "other:" then pure (.other (s.drop 6).toString)
    else throw s!"unknown expectation {s}"

def Expect.holds (e : Expect) (decoded : Bool) (o : Except Failure ReturnData) : Bool :=
  match e, o with
  | .ok, .ok _ => true
  | .fail, .error _ => true
  | .noCall, .error _ => !decoded
  | .outOfGas, .error .outOfGas => true
  | .balanceExceeded, .error .balanceExceeded => true
  | .lackBalanceForState, .error (.lackBalanceForState _) => true
  | .methodNotFound, .error .methodNotFound => true
  | .panic sub, .error (.panic msg) => sub.isEmpty || (msg.splitOn sub).length > 1
  | .other sub, .error (.other msg) => sub.isEmpty || (msg.splitOn sub).length > 1
  | _, _ => false

/-! ## The world -/

/-- A receipt the contract created, addressable as `label#index`. -/
structure Pending where
  receipt : RawReceipt
  signer : AccountId

structure World (M : ExecModel) where
  trie : Near.TrieOverlay.State
  model : Option M.State
  balance : Nat
  locked : Nat
  usage : Nat
  height : Nat
  timestamp : Nat
  pending : List (String × Pending) := []
  /-- Discrepancies found by probes. -/
  findings : List (List String) := []

structure Env where
  protocol : RuntimeConfig
  code : Near.Boundary.Code
  contract : AccountId
  verbose : Bool

/-- The contract's records in the trie, sorted by key (the order the VM's
initial state uses; any listing gives the same observation). -/
def contractListing (env : Env) (trie : Near.TrieOverlay.State) : List (RawBytes × RawBytes) :=
  let pre := Near.TrieOverlay.contractKey env.contract.bytes []
  let records := trie.view.filterMap fun (key, value) =>
    if pre.isPrefixOf key then some (key.drop pre.length, value) else none
  records.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- One step's failure. `scenario` is a broken scenario or hypothesis, not a discrepancy. -/
structure StepError where
  scenario : Bool
  lines : List String

abbrev RunM := ExceptT StepError IO

def scenarioError (msg : String) : RunM α := throw { scenario := true, lines := [msg] }

def liftScenario (x : Except String α) : RunM α :=
  match x with
  | .ok a => pure a
  | .error e => scenarioError e

/-! ## One receipt -/

/-- Everything a call varies; the world supplies the rest of the context. -/
structure CallInput where
  method : String
  args : RawBytes
  predecessor : AccountId
  signer : AccountId
  attached : Nat
  gas : GasSpec
  results : List PromiseResult
  /-- Receivers of the call's result (`output_data_receivers`). -/
  outputs : List AccountId := []
  /-- A constant recorded storage proof (`Context.storageProofSize`), when set. -/
  proofSize : Option Nat := none

def RolledBackB (ctx : Context) (raw : RawStorage) (r : Observation) : Bool :=
  (match r.outcome with | .error _ => true | .ok _ => false) && decide (r.storage = raw) &&
    r.balance == ctx.balance && r.storageUsage == ctx.storageUsage && r.receipts.isEmpty

/-- `Matches` as a boolean, with the reasons it fails. -/
def matchesWhy (M : ExecModel) (ctx : Context) (raw : RawStorage) (r : Observation) :
    StepResult M.Panic M.State M.Ret M.Promise → List String
  | .ok o =>
    let receipts := M.encodeReceipts (ctx.prepaidGas - r.usedGas) o.promises
    let ret := M.encodeRet o.ret
    let balance := ctx.balance + ctx.attached - receiptDeposits receipts
    let usage := ctx.storageUsage - storageUsageOf ctx.protocol raw +
      storageUsageOf ctx.protocol (M.encodeState o.state)
    (if (match r.outcome with | .ok d => d == ret | .error _ => false) then []
      else [s!"outcome: binary {showOutcome r.outcome}, model ok ({showReturn ret})"]) ++
    (if decide (r.storage = M.encodeState o.state) then [] else
      let extra := r.storage \ M.encodeState o.state
      let missing := M.encodeState o.state \ r.storage
      [s!"storage: binary has {extra.card} records the model does not, model {missing.card} the binary does not"]) ++
    (if r.balance == balance then [] else [s!"balance: binary {r.balance}, model {balance}"]) ++
    (if r.storageUsage == usage then [] else [s!"storage usage: binary {r.storageUsage}, model {usage}"]) ++
    (if r.logs == o.logs then [] else [s!"logs: binary {showLogs r.logs}, model {showLogs o.logs}"]) ++
    (if r.receipts == receipts then [] else
      ["receipts differ:"] ++ (r.receipts.map fun x => s!"  binary {showReceipt x}") ++
        (receipts.map fun x => s!"  model  {showReceipt x}"))
  | .error f =>
    let failure := M.failure f.failure
    (if (match r.outcome with | .error e => decide (e = failure) | .ok _ => false) then []
      else [s!"outcome: binary {showOutcome r.outcome}, model error {repr failure |>.pretty}"]) ++
    (if decide (r.storage = raw) then [] else ["storage changed on a model failure"]) ++
    (if r.balance == ctx.balance then [] else [s!"balance: binary {r.balance}, before {ctx.balance}"]) ++
    (if r.storageUsage == ctx.storageUsage then [] else
      [s!"storage usage: binary {r.storageUsage}, before {ctx.storageUsage}"]) ++
    (if r.logs == f.logs then [] else [s!"logs: binary {showLogs r.logs}, model {showLogs f.logs}"]) ++
    (if r.receipts.isEmpty then [] else ["receipts created on a model failure"])

def stepResultName (M : ExecModel) : StepResult M.Panic M.State M.Ret M.Promise → String
  | .ok o => s!"ok ({showReturn (M.encodeRet o.ret)})"
  | .error f => s!"error {repr (M.failure f.failure) |>.pretty}"

/-- The hypotheses of `Refines` for this context: the storage represents the
model state, and the parts of `Context.WF` a scenario can break. -/
def checkHypotheses (M : ExecModel) (ctx : Context) (raw : RawStorage) (st : Option M.State) :
    List String :=
  (match st with
    | none => if raw.card == 0 then [] else ["storage is not empty but the model has no state"]
    | some s =>
      (if decide (raw = M.encodeState s) then [] else ["storage does not encode the model state"]) ++
      ((M.invViolation s).map (s!"model state breaks the invariant: {·}")).toList) ++
  (if ctx.balance + ctx.attached < 2 ^ 128 then [] else ["balance + attached ≥ 2^128"]) ++
  (if ctx.locked < 2 ^ 128 then [] else ["locked ≥ 2^128"]) ++
  (if ctx.prepaidGas < 2 ^ 64 then [] else ["prepaid gas ≥ 2^64"]) ++
  (if storageUsageOf ctx.protocol raw ≤ ctx.storageUsage then []
    else ["storage usage does not count the contract records"]) ++
  (if ctx.storageUsage + ctx.protocol.wasm.limits.maxGasBurnt < 2 ^ 64 then []
    else ["storage usage leaves no room"])

/-- Run one call; return the observation and whether the input was a call. -/
def runCall (M : ExecModel) (env : Env) (w : World M) (label : String) (c : CallInput)
    (expect : Option Expect) : RunM (World M × Observation) := do
  let storage := contractListing env w.trie
  let raw := storage.toFinset
  let mkCtx (gas : Nat) : Context :=
    { method := c.method, args := c.args, current := env.contract, predecessor := c.predecessor,
      signer := c.signer, signerPk := [], attached := c.attached, prepaidGas := gas,
      promiseResults := c.results, outputDataReceivers := c.outputs, balance := w.balance,
      locked := w.locked, storageUsage := w.usage, blockHeight := w.height,
      timestamp := w.timestamp, epochHeight := 1, randomSeed := List.replicate 32 0,
      trie := w.trie, protocol := env.protocol,
      storageProofSize := c.proofSize.map fun n _ => n }
  let call := M.decode c.method c.args
  let gas ← match c.gas, call with
    | .exact g, _ => pure g
    | .bound d, some call =>
      -- The bound may depend on the prepaid gas (gas the call forwards): the
      -- least prepaid gas whose bound fits its limit, by bisection.
      let fits (g : Nat) := decide (M.gas (mkCtx g) w.model call ≤ (mkCtx g).gasLimit)
      let rec least (lo hi : Nat) (fuel : Nat) : Nat :=
        match fuel with
        | 0 => hi
        | fuel + 1 =>
          if hi ≤ lo + 1 then hi
          else
            let mid := (lo + hi) / 2
            if fits mid then least lo mid fuel else least mid hi fuel
      let top := 10 ^ 15
      unless fits top do scenarioError s!"{label}: no prepaid gas fits the model's bound"
      let b := if fits 0 then 0 else least 0 top 64
      pure (Int.toNat (b + d))
    | .bound _, none => scenarioError s!"{label}: gas \"bound\" needs an input that is a call"
  let ctx := mkCtx gas
  let hyps := checkHypotheses M ctx raw w.model
  unless hyps.isEmpty do scenarioError s!"{label}: hypothesis of Refines violated: {hyps}"
  let r := Near.Boundary.execOn env.code storage ctx
  let header := s!"{label}: {c.method} by {c.predecessor.val}, {tgas gas} prepaid"
  let mut problems : List String := []
  if let .error (.executionIssue msg) := r.outcome then
    problems := problems ++ [s!"execution issue: {msg}"]
  let mut info := ""
  match call with
  | none =>
    unless RolledBackB ctx raw r do
      problems := problems ++ [s!"input that is no call did not fail with no effects: {showOutcome r.outcome}"]
    info := s!"no call → {showOutcome r.outcome}"
  | some call =>
    let res := M.step ctx w.model call
    let bound := M.gas ctx w.model call
    let why := matchesWhy M ctx raw r res
    if bound ≤ ctx.gasLimit then
      problems := problems ++ why
      unless r.usedGas ≤ bound do
        problems := problems ++ [s!"used gas {r.usedGas} exceeds the model's bound {bound}"]
    else
      let oog := (match r.outcome with | .error .outOfGas => true | _ => false) &&
        RolledBackB ctx raw r && r.logs.isPrefixOf res.logs
      unless why.isEmpty || oog do
        problems := problems ++ ["below the bound: neither Matches nor an out-of-gas failure with no effects"] ++ why
    unless problems.isEmpty do
      problems := problems ++ [s!"model: {M.callName call} → {stepResultName M res}"]
    info := s!"{M.callName call} → {showOutcome r.outcome}, used {tgas r.usedGas} of bound {tgas bound}"
  unless problems.isEmpty do
    throw { scenario := false,
            lines := [s!"DISCREPANCY {header}", s!"  binary: {showOutcome r.outcome}, logs {showLogs r.logs}"] ++
              problems.map ("  " ++ ·) }
  if let some e := expect then
    unless e.holds call.isSome r.outcome do
      scenarioError s!"{label}: expectation not met: {info}"
  if env.verbose then IO.println s!"  ok {label}: {info}"
  -- Advance by the binary's observation; the model follows the matched outcome.
  let committed := match Near.TrieOverlay.step env.contract.bytes .commit r.trie with
    | .ok (t, _) => t
    | .error _ => r.trie
  match r.outcome, call with
  | .ok _, some call =>
    match M.step ctx w.model call with
    | .ok o =>
      let pending := r.receipts.zipIdx.map fun (x, i) => (s!"{label}#{i}", { receipt := x, signer := c.signer })
      pure ({ w with trie := committed, model := some o.state, balance := r.balance,
                     usage := r.storageUsage, pending := w.pending ++ pending }, r)
    | .error _ => scenarioError s!"{label}: unreachable (matched a model failure with a success)"
  | _, _ => pure ({ w with trie := committed }, r)

/-! ## Scenarios -/

/-- `outputDataReceivers`: account ids, each a string or `{"repeat": id, "times": n}`. -/
def outputsOf (j : Json) : Except String (List AccountId) :=
  match field? j "outputDataReceivers" with
  | none => pure []
  | some v => do
    let arr ← v.getArr?
    let parts ← arr.toList.mapM fun p => match p with
      | .str s => do pure [← accountOf s]
      | p => do
        let a ← accountOf (← strD p "repeat" "")
        pure (List.replicate (← natD p "times" 1) a)
    pure parts.flatten

def callInputOf (j : Json) (signerDefault : Option AccountId) : Except String CallInput := do
  let fromS ← strD j "from" "alice.near"
  let predecessor ← accountOf fromS
  let signer ← match field? j "signer", signerDefault with
    | some (.str s), _ => accountOf s
    | _, some s => pure s
    | _, none => pure predecessor
  pure { method := ← strD j "method" "", args := ← argsOf j, predecessor, signer,
         attached := ← natD j "deposit" 0,
         gas := ← (match field? j "gas" with | some g => gasSpecOf g | none => pure (.exact (300 * 10 ^ 12))),
         results := (← resultsOf j).getD [], outputs := ← outputsOf j,
         proofSize := ← (match field? j "storageProofSize" with
           | some v => (some ·) <$> natOf v
           | none => pure none) }

/-- A delivered receipt as a call: its action, by the contract, under the
original signer. Transfers to the contract are credits. -/
def deliver (M : ExecModel) (env : Env) (w : World M) (label ref : String) (j : Json)
    (expect : Option Expect) : RunM (World M) := do
  let some p := w.pending.lookup ref
    | if field? j "optional" matches some (.bool true) then return w
      else scenarioError s!"{label}: no pending receipt {ref} (pending: {w.pending.map (·.1)})"
  unless p.receipt.receiverId == env.contract.bytes do
    scenarioError s!"{label}: {ref} goes to {showBytes p.receipt.receiverId}, not the contract; supply its result to the callback instead"
  let results ← liftScenario (resultsOf j)
  if results.isNone && !p.receipt.dependencies.isEmpty then
    scenarioError s!"{label}: {ref} waits on {p.receipt.dependencies.length} receipt(s); give their results"
  let keep := w.pending.filter (·.1 != ref)
  match p.receipt.actions with
  | [.transfer amount] =>
    if env.verbose then IO.println s!"  ok {label}: transfer of {amount} arrives"
    pure { w with balance := w.balance + amount, pending := keep }
  | [.functionCall m args deposit gas] =>
    let method ← match String.fromUTF8? ⟨m.toArray⟩ with
      | some s => pure s
      | none => scenarioError s!"{label}: method name is not UTF-8"
    let gasSpec ← match field? j "gas" with
      | some g => liftScenario (gasSpecOf g)
      | none => pure (.exact gas.toNat)
    let (w, _) ← runCall M env { w with pending := keep } label
      { method, args, predecessor := env.contract, signer := p.signer, attached := deposit,
        gas := gasSpec, results := results.getD [], outputs := ← liftScenario (outputsOf j) } expect
    pure w
  | _ => scenarioError s!"{label}: only single-action receipts can be delivered"

def runReceipt' (M : ExecModel) (env : Env) (w : World M) (label : String) (j : Json) :
    RunM (World M) := do
  let expect ← match field? j "expect" with
    | some (.str s) => liftScenario ((some ·) <$> expectOf s)
    | _ => pure none
  if let some c := field? j "call" then
    let input ← liftScenario (callInputOf c none)
    return (← runCall M env w label input expect).1
  if let some (.str ref) := field? j "deliver" then
    return ← deliver M env w label ref j expect
  if let some a := field? j "credit" then
    return { w with balance := w.balance + (← liftScenario (natOf a)) }
  if let some a := field? j "debit" then
    let a ← liftScenario (natOf a)
    if a > w.balance then scenarioError s!"{label}: debit exceeds the balance"
    return { w with balance := w.balance - a }
  scenarioError s!"{label}: unknown receipt {j.compress}"

/-- A block: commit the previous chunk's writes into a fresh trie with a cold cache. -/
def newBlock (M : ExecModel) (w : World M) (height timestamp : Nat) : RunM (World M) := do
  match Near.TrieOverlay.start w.trie.view with
  | .ok trie => pure { w with trie, height, timestamp }
  | .error e => scenarioError s!"trie: {e}"

/-- Trie records outside the contract: `trie: [{"account", "key", "value"}]`. -/
def otherRecords (j : Json) : Except String (List (RawBytes × RawBytes)) := do
  match field? j "trie" with
  | none => pure []
  | some v =>
    let arr ← v.getArr?
    arr.toList.mapM fun r => do
      let account ← accountOf (← strD r "account" "")
      let key ← bytesOf (← r.getObjVal? "key")
      let value ← bytesOf (← r.getObjVal? "value")
      pure (Near.TrieOverlay.contractKey account.bytes key, value)

/-- A receipt; a `probe` runs on the current world and leaves it unchanged,
recording a discrepancy instead of stopping the scenario. -/
def runReceipt (M : ExecModel) (env : Env) (w : World M) (label : String) (j : Json) :
    RunM (World M) := do
  match field? j "probe" with
  | some (.bool true) =>
    try
      let _ ← runReceipt' M env w label j
      pure w
    catch e =>
      if e.scenario then throw e else pure { w with findings := w.findings ++ [e.lines] }
  | _ => runReceipt' M env w label j

structure Summary where
  name : String
  receipts : Nat
  error : Option StepError

def runScenario (M : ExecModel) (base : Env) (j : Json) : IO Summary := do
  let name := (strD j "name" "?").toOption.getD "?"
  let go : RunM Nat := do
    let contract ← liftScenario (accountOf (← liftScenario (strD j "contract" base.contract.val)))
    let env := { base with contract }
    let (st, records) ← liftScenario (M.initial ((field? j "state").getD Json.null))
    let account := (field? j "account").getD (Json.mkObj [])
    let balance ← liftScenario (natD account "balance" (100 * 10 ^ 24))
    let locked ← liftScenario (natD account "locked" 0)
    let overhead ← liftScenario (natD account "overhead" 1000)
    let others ← liftScenario (otherRecords j)
    let entries := records.map (fun (k, v) => (Near.TrieOverlay.contractKey contract.bytes k, v)) ++ others
    let trie ← match Near.TrieOverlay.start entries with
      | .ok t => pure t
      | .error e => scenarioError s!"trie: {e}"
    let usage := overhead + storageUsageOf env.protocol records.toFinset
    let mut w : World M := { trie, model := st, balance, locked, usage, height := 0, timestamp := 0 }
    let blocks ← liftScenario (do (← j.getObjVal? "blocks").getArr?)
    let mut count := 0
    let mut bi := 0
    for b in blocks do
      bi := bi + 1
      let height ← liftScenario (natD b "height" (w.height + 1))
      if height ≤ w.height then scenarioError s!"block {bi}: height {height} does not increase"
      let timestamp ← liftScenario (natD b "timestamp" (height * 10 ^ 9))
      w ← newBlock M w height timestamp
      let receipts ← liftScenario (do (← b.getObjVal? "receipts").getArr?)
      let mut ri := 0
      for r in receipts do
        ri := ri + 1
        let label ← liftScenario (strD r "label" s!"h{height}.{ri}")
        w ← runReceipt M env w label r
        count := count + 1
    unless w.findings.isEmpty do
      throw { scenario := false, lines := w.findings.flatten }
    pure count
  if base.verbose then IO.println s!"scenario {name}"
  match ← go.run with
  | .ok n => pure { name, receipts := n, error := none }
  | .error e => pure { name, receipts := 0, error := some e }

end Scenario
