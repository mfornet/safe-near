import Lean.Data.Json
import NearFastVM.Run

/-!
# Comparing the fast engine with the specification

`outcomeKey` renders every field of a `VMOutcome`; two runs agree when their keys are equal. `machineDiff`
compares the machines themselves (values or trap, the error, the burnt gas and its profile, memory and
globals) for the part of a run that `NearFastVM.execute` replaces.
-/

namespace FastVMTests

open Lean Wasm Wasm.Near NearFastVM

def bytesJson (bytes : List UInt8) : Json :=
  toJson (bytes.map UInt8.toNat)

def obj :=
  Json.mkObj

def kind (name : String) : String × Json :=
  ("kind", toJson name)

def permissionJson : AccessKeyPermission → Json
  | .fullAccess => obj [kind "fullAccess"]
  | .functionCall allowance receiver methods =>
    obj
      [kind "functionCall", ("allowance", toJson (allowance.map toString)),
        ("receiverId", bytesJson receiver), ("methodNames", bytesJson methods)]
  | .gasKeyFullAccess nonces => obj [kind "gasKeyFullAccess", ("numNonces", toJson nonces)]
  | .gasKeyFunctionCall nonces allowance receiver methods =>
    obj
      [kind "gasKeyFunctionCall", ("numNonces", toJson nonces),
        ("allowance", toJson (allowance.map toString)), ("receiverId", bytesJson receiver),
        ("methodNames", bytesJson methods)]

def actionJson : PromiseAction → Json
  | .createAccount => obj [kind "createAccount"]
  | .deployContract code => obj [kind "deployContract", ("code", bytesJson code)]
  | .functionCall method args amount gas =>
    obj
      [kind "functionCall", ("method", bytesJson method), ("args", bytesJson args),
        ("deposit", toJson (toString amount)), ("gas", toJson gas.toNat)]
  | .transfer amount => obj [kind "transfer", ("deposit", toJson (toString amount))]
  | .stake amount pk =>
    obj [kind "stake", ("stake", toJson (toString amount)), ("publicKey", bytesJson pk)]
  | .addKey pk nonce permission =>
    obj
      [kind "addKey", ("publicKey", bytesJson pk), ("nonce", toJson nonce.toNat),
        ("permission", permissionJson permission)]
  | .deleteKey pk => obj [kind "deleteKey", ("publicKey", bytesJson pk)]
  | .deleteAccount beneficiary =>
    obj [kind "deleteAccount", ("beneficiaryId", bytesJson beneficiary)]
  | .useGlobalContract (.codeHash hash) =>
    obj [kind "useGlobalContract", ("codeHash", bytesJson hash)]
  | .useGlobalContract (.accountId id) =>
    obj [kind "useGlobalContract", ("accountId", bytesJson id)]
  | .deployGlobalContract code mode =>
    obj
      [kind "deployGlobalContract", ("code", bytesJson code),
        ("mode",
          toJson
            (match mode with
            | .codeHash => "codeHash"
            | .accountId => "accountId"))]
  | .transferToGasKey pk amount =>
    obj
      [kind "transferToGasKey", ("publicKey", bytesJson pk), ("deposit", toJson (toString amount))]

def receiptJson (receipt : ReceiptSpec) : Json :=
  obj
    [("receiverId", bytesJson receipt.receiverId), ("dependencies", toJson receipt.dependencies),
      ("yieldDataId", toJson (receipt.yieldDataId.map bytesJson)),
      ("actions", toJson (receipt.actions.map actionJson))]

def returnJson : ReturnData → Json
  | .none => obj [kind "none"]
  | .value bytes => obj [kind "value", ("bytes", bytesJson bytes)]
  | .receiptIndex index => obj [kind "receipt", ("index", toJson index)]

/-- Every observable field of an outcome, as one string. -/
def outcomeKey (outcome : VMOutcome) : String :=
  let storage := outcome.storage.mergeSort (fun a b => bytesLe a.1 b.1)
  (obj
      [("balance", toJson (toString outcome.balance)),
        ("storageUsage", toJson outcome.storageUsage),
        ("returnData", returnJson outcome.returnData), ("gasBurnt", toJson outcome.burntGas),
        ("gasUsed", toJson outcome.usedGas), ("distributed", toJson outcome.distributedGas),
        ("logs", toJson outcome.logs),
        ("storage", toJson (storage.map fun (k, v) => (k.map UInt8.toNat, v.map UInt8.toNat))),
        ("receipts", toJson (outcome.receipts.map receiptJson)),
        ("resumes",
          toJson
            (outcome.resumes.map fun (dataId, payload) =>
              obj [("dataId", bytesJson dataId), ("payload", bytesJson payload)])),
        ("aborted", toJson (outcome.aborted.map (·.message))),
        ("abortedKind", toJson (outcome.aborted.map fun e => (repr e).pretty)),
        ("subsidizedAmount", toJson (toString outcome.subsidizedAmount)),
        ("gasProfile",
          obj
            [("ext", toJson (outcome.gasProfile.ext.map fun (name, gas) => s!"{name}={gas}")),
              ("actionBurnt", toJson outcome.gasProfile.actionBurnt),
              ("wasm", toJson outcome.gasProfile.wasm)])]).compress

/-! ## Machines -/

def valueKey : Value → String
  | .i32 v => s!"i32:{v}"
  | .i64 v => s!"i64:{v}"
  | .f32 v => s!"f32:{v}"
  | .f64 v => s!"f64:{v}"
  | .ref _ => "ref"

def pageKey (p : ByteArray) : ByteArray :=
  if p.size == 0 then zeroPage else p

/-- A description of how two final machines differ, or `none`. -/
def machineDiff (spec fast : Machine × Option FunctionCallError) : Option String :=
  let (m1, e1) := spec
  let (m2, e2) := fast
  let head : Machine → String
    | .done vs _ => s!"done {vs.map valueKey}"
    | .trap t _ => s!"trap {t.message}"
    | .next _ => "next"
  let err : Option FunctionCallError → String := fun e =>
    match e with
    | none => "ok"
    | some e => (repr e).pretty
  -- an error ends the run in some machine whose store is the point of comparison, not its kind
  let h1 := if e1.isSome then "stopped" else head m1
  let h2 := if e2.isSome then "stopped" else head m2
  if h1 != h2 || err e1 != err e2 then some s!"result: spec {h1} {err e1}, fast {h2} {err e2}"
  else
    let s1 := m1.store
    let s2 := m2.store
    let g1 := s1.host.gas
    let g2 := s2.host.gas
    if
        g1.burnt != g2.burnt || g1.promises != g2.promises || g1.prepaid != g2.prepaid ||
          g1.maxBurnt != g2.maxBurnt then
      some s!"gas: spec {g1.burnt}/{g1.promises}, fast {g2.burnt}/{g2.promises}"
    else
      if (repr s1.host.gasProfile).pretty != (repr s2.host.gasProfile).pretty then
        some "gas profile"
      else
        if s1.mems.size != s2.mems.size then some "memory count"
        else
          let memDiff :=
            Id.run do
              for k in [0:s1.mems.size] do
                let a := s1.mems[k]!
                let b := s2.mems[k]!
                if a.pages.size != b.pages.size then
                  return some s!"memory {k}: size"
                for p in [0:a.pages.size] do
                  let x := a.pages[p]!
                  let y := b.pages[p]!
                  unless x.size == 0 && y.size == 0 do
                    if pageKey x != pageKey y then
                      return some s!"memory {k}: page {p}"
              return none
          match memDiff with
          | some d => some d
          | none =>
            if s1.globals.size != s2.globals.size then some "global count"
            else
              let gd :=
                Id.run do
                  for k in [0:s1.globals.size] do
                    if valueKey s1.globals[k]!.value != valueKey s2.globals[k]!.value then
                      return some
                          s!"global {k}: spec {valueKey s1.globals[k]!.value}, fast {valueKey s2.globals[k]!.value}"
                  return none
              gd

/-! ## Random numbers -/

/-- SplitMix64. -/
structure Rng where
  state : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), { state := s })

abbrev Gen :=
  StateM Rng

def rand : Gen UInt64 :=
  modifyGet Rng.next

def below (n : Nat) : Gen Nat := do
  let v ← rand
  return if n == 0 then 0 else (v % n.toUInt64).toNat

def chance (num den : Nat) : Gen Bool := do
  return (← below den) < num

def pick (xs : Array α) [Inhabited α] : Gen α := do
  return xs[← below xs.size]!

end FastVMTests
