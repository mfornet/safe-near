import Spec.Contract
import Spec.Exports
import Proofs.Availability
import NearRuntime.BoundaryResolution
import Lean

/-!
# The refinement obligation (open)

`Spec/Contract.lean` gives the wNEAR `ContractModel`; `NearRuntime.Boundary`
gives near-lean's `RuntimeInterface`, a function-call action followed by the
receipt's storage-stake check. This file pins the deployed binary and the
protocol configuration, so that `refines_wnear` below is a closed statement
about `contract.wasm` under that configuration.

The binary is embedded as a hex string, read when this file is elaborated.
Decoding it in the kernel exceeds the available memory, so the decoded module
and two facts about it (no start function; the exported functions) are
hypotheses, which the adapter tests (`just runtime-adapter-test`) check on the
binary.

The protocol configuration is pinned the same way: the JSON of the latest
config in `near-lean/vm/configs`, the one the adapter tests run on, is
embedded, and the parsed configuration is a hypothesis. Gas costs and limits
are protocol parameters: `gasBound` is a sum of constants measured under this
configuration, and the binary's logs and register reads succeed only under
its limits, so the statement does not hold for every configuration.

`refines_wnear_exported` (the 15 exported methods) is the only open proof in
this project; `refines_wnear` and its corollaries depend on it. `just wnear-audit`
tolerates `sorryAx` in this module alone.
-/

namespace WNear

open NearInterface

open Lean Elab Term in
/-- The bytes of a file, as a hex string literal, read when this file is
elaborated. Paths are relative to the package root. -/
elab "file_hex%" path:str : term => do
  let bytes ← IO.FS.readBinFile path.getString
  let hex := String.join (bytes.toList.map fun b =>
    String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)])
  return mkStrLit hex

open Lean Elab Term in
/-- The text of a file, as a string literal, read when this file is
elaborated. Paths are relative to the package root. -/
elab "file_text%" path:str : term => do
  return mkStrLit (← IO.FS.readFile path.getString)

/-- Bytes from a lowercase hex string. -/
def bytesOfHex (s : String) : ByteArray :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (digit a * 16 + digit b) :: go rest
    | _ => []
  ⟨(go s.toList).toArray⟩

/-- `contract.wasm`, as deployed. -/
def wNearHex : String := file_hex% "../contract.wasm"

def wNearBytes : ByteArray := bytesOfHex wNearHex

/-- The protocol version the statement is pinned to. -/
def wNearProtocolVersion : Nat := 86

/-- The pinned version is the latest config, the one the adapter tests load:
a new config breaks this until the statement is re-pinned. -/
example : wNearProtocolVersion = Wasm.Near.RuntimeConfig.latestVersion := rfl

/-- `runtime_config_v86.json`, nearcore's `RuntimeConfigView` at version 86. -/
def wNearProtocolJson : String := file_text% "../../../near-lean/vm/configs/runtime_config_v86.json"

theorem exportFunc_none {m : Wasm.Module} {name : String} (h : name ∉ funcExportNames m) :
    m.exportFunc? name = none := by
  unfold Wasm.Module.exportFunc?
  rw [← Array.findSome?_toList, List.findSome?_eq_none_iff]
  intro e he
  split
  · rename_i i hd
    split
    · rename_i hn
      exact absurd (List.mem_filterMap.mpr ⟨e, he, by simp [hd, beq_iff_eq.mp hn]⟩) h
    · rfl
  · rfl

/-- Methods the binary does not export are no calls. -/
theorem decode_not_exported {method : String} (h : method ∉ exportedMethods) (args : List UInt8) :
    Call.decode method args = none := by
  simp only [exportedMethods, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  unfold Call.decode
  split <;> simp_all

/-- **Open.** The exported methods: on a call to one of them under the pinned
protocol configuration, near-lean's execution of `contract.wasm` is the
model's as `Refines` states it. -/
theorem refines_wnear_exported (cfg : Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (raw : RawStorage) (st : Option State) (ctx : Context) (hrep : (wnear cfg).Represents raw st)
    (hwf : ctx.WF raw) (hprot : ctx.protocol = protocol) (hmethod : ctx.method ∈ exportedMethods) :
    let r := Near.Boundary.nearRuntime.exec
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } raw ctx
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    (∀ c, (wnear cfg).Parses ctx.method ctx.args c →
      let res := (wnear cfg).step ctx st c
      ((wnear cfg).gas ctx st c ≤ ctx.gasLimit →
        Matches (wnear cfg) ctx raw r res ∧ r.usedGas ≤ (wnear cfg).gas ctx st c) ∧
      (Matches (wnear cfg) ctx raw r res ∨
        (r.outcome = .error .outOfGas ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs))) ∧
    ((¬ ∃ c, (wnear cfg).Parses ctx.method ctx.args c) → RolledBack ctx raw r) := by
  sorry

/-- The deployed wNEAR binary refines the model: for every configuration whose
measured account entry fits a `u64`, every context under the pinned protocol
configuration (version 86) and every resource state, near-lean's execution of
`contract.wasm` is the model's as `Refines` states it. `codeOf` decodes code that the call's promises deploy; wNEAR deploys none.
Proved for every method the binary does not export; open for the exported
ones (`refines_wnear_exported`). -/
@[blueprint "spec:refinement"
  (statement := /-- The deployed binary refines \cref{def:contract-model} under the pinned protocol configuration (version 86): for every storage representing a model state and every context the runtime can build with that configuration, the execution reports no interpreter limitation; with at least the model's gas bound attached, it agrees with the model on return value, storage, balance, storage usage, logs, receipts and failure, and uses at most that much gas; with less, it agrees or fails for gas with no effects; and input that is no call fails with no effects. -/)]
theorem refines_wnear (cfg : Config) (code : Wasm.Module) (codeOf : List UInt8 → Near.ContractCode)
    (protocol : Wasm.Near.RuntimeConfig)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (hstart : code.start = none) (hexports : funcExportNames code = exportedMethods) :
    Refines Near.Boundary.nearRuntime protocol
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } (wnear cfg) := by
  intro raw st ctx hrep hwf hprot
  by_cases hmethod : ctx.method ∈ exportedMethods
  · exact refines_wnear_exported cfg code codeOf protocol hcfg hcode hprotocol raw st ctx hrep hwf
      hprot hmethod
  · have hexport : code.exportFunc? ctx.method = none := exportFunc_none (by rw [hexports]; exact hmethod)
    obtain ⟨hrb, hni⟩ := Near.Boundary.nearRuntime_not_exported
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } raw ctx rfl
      hstart hexport
    have hnone : ∀ c, ¬ (wnear cfg).Parses ctx.method ctx.args c := by
      intro c hc
      change Call.decode ctx.method ctx.args = some c at hc
      rw [decode_not_exported hmethod] at hc
      cases hc
    exact ⟨hni, fun c hc => absurd hc (hnone c), fun _ => hrb⟩

/-- `withdraw_available_binary` for `contract.wasm` on near-lean under the
pinned protocol configuration: a withdrawal attached with at least the model's gas bound succeeds on the deployed binary.
It depends on `refines_wnear`, which a withdrawal reaches through the open
`refines_wnear_exported`, so the audit lists it as open too. -/
theorem withdraw_available_wasm (cfg : Config) (code : Wasm.Module)
    (codeOf : List UInt8 → Near.ContractCode) (protocol : Wasm.Near.RuntimeConfig)
    (hcfg : cfg.WF) (hcode : Wasm.Binary.decode wNearBytes = .ok code)
    (hprotocol : Wasm.Near.RuntimeConfig.parse wNearProtocolJson = .ok protocol)
    (hstart : code.start = none) (hexports : funcExportNames code = exportedMethods)
    {s : State} {ctx : Context} {amount : Nat}
    (hs : Inv cfg s) (hwf : ctx.WF (encode s)) (hprot : ctx.protocol = protocol)
    (hparse : Parses ctx.method ctx.args (.nearWithdraw amount))
    (hreg : AccountId.ofNear ctx.predecessor ∈ s.registered)
    (hamt : amount ≤ s.balance (AccountId.ofNear ctx.predecessor)) (hdep : ctx.attached = 1)
    (hbound : amount + 1 < u128Bound) (hbal : amount ≤ ctx.balance)
    (hrent : stakeDeficit ctx.protocol (usageAfter ctx (some s)
      { s.setBalance (AccountId.ofNear ctx.predecessor)
          (s.balance (AccountId.ofNear ctx.predecessor) - amount) with
        totalSupply := s.totalSupply - amount }) (ctx.balance - amount) ctx.locked = 0)
    (hlog : logLimitError ctx.protocol
      [s!"Withdraw {amount} NEAR from {AccountId.ofNear ctx.predecessor}"] = none)
    (hreceipts : ReceiptValidation.callReceiptsError ctx.protocol ctx.current ctx.signer ctx.signerPk
      (encodeReceipts [.transfer (AccountId.ofNear ctx.predecessor) (amount + 1)]) = none)
    (hgas : gasBound ctx (.nearWithdraw amount) ≤ ctx.gasLimit) :
    let r := Near.Boundary.nearRuntime.exec
      { code := { module := code, size := wNearBytes.size, hash := "" }, codeOf } (encode s) ctx
    r.outcome = .ok (.receiptIndex 0) ∧
      r.storage =
        encode { s.setBalance (AccountId.ofNear ctx.predecessor)
            (s.balance (AccountId.ofNear ctx.predecessor) - amount) with
          totalSupply := s.totalSupply - amount } :=
  withdraw_available_binary (refines_wnear cfg code codeOf protocol hcfg hcode hprotocol hstart hexports)
    hs hwf hprot hparse hreg hamt hdep hbound hbal hrent hlog hreceipts hgas

end WNear
