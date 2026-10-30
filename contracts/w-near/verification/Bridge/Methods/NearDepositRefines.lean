import Bridge.Methods.NearDepositSuccessAgreement
import Bridge.Methods.NearDepositPanicAgreement

/-!
# Initialized `near_deposit`: refinement, conditional on the remaining gas bound

All functional agreement and host-precondition obligations are discharged. The only
method-specific premise left is that loading plus `costDep` fits the model's gas bound.
Protocol costs and limits remain explicit until the final pinning step.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.DepositBody
open WNear.Binary.FtTotalSupplyMethod (CostsV86 LimitsV86)

/-- The initialized method satisfies every per-call refinement clause once its quantitative
gas bound is supplied. This is not yet the unconditional protocol-86 method theorem. -/
theorem nearDeposit_refines_init_of_bound (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (s : WNear.State)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hrep : (WNear.wnear cfg).Represents raw (some s)) (hm : ctx.method = "near_deposit")
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hv : 29 ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hn : 1 ≤ ctx.protocol.wasm.limits.maxNumberLogs)
    (husage : 85 + ctx.protocol.fees.numExtraBytesRecord ≤ ctx.protocol.wasm.limits.maxGasBurnt)
    (hbound : chargesUse (hostOf ctx raw) (loadingCharges size) +
      costDep ctx.protocol s (regOf s (.ofNear ctx.predecessor)) (erase (hostOf ctx raw)) ≤
        (WNear.wnear cfg).gas ctx (some s) .nearDeposit) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some s) .nearDeposit
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some s) .nearDeposit ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some s) .nearDeposit) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some s) .nearDeposit) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨hinv, hraw⟩ := (show WNear.Inv cfg s ∧ raw = WNear.encode s from hrep)
  have hs := hinv.toWF
  let reg := regOf s (.ofNear ctx.predecessor)
  let c := caseDep (erase (hostOf ctx raw)) s reg
  have cases_agree (h : NearState) (he : eraseP h = eraseP (hostOf ctx raw)) : caseDep h s reg = c :=
    (caseDep_eq_model ctx raw s hwf hs h he).trans
      (caseDep_eq_model ctx raw s hwf hs (erase (hostOf ctx raw)) rfl).symm
  have hU : ctx.storageUsage + (85 + ctx.protocol.fees.numExtraBytesRecord) < 2 ^ 64 := by
    have hu := hwf.usage_room
    omega
  have effects (h h' : NearState) (he : eraseP h = eraseP (hostOf ctx raw))
      (hq : postDepOk ctx.protocol.fees.numExtraBytesRecord s reg h h') :
      DepositEffects ctx.protocol.fees.numExtraBytesRecord h s reg h' := by
    apply postDepOk_effects ?_ (regOf_storage ctx raw s hwf hraw h he) hq
    rw [eraseP_field he NearState.storage (fun _ => rfl)]
    exact FtTotalSupplyMethod.hostOf_storage_of_mem hwf (by rw [hraw]; exact WNear.mem_encode_header.mpr rfl)
  have noPromises (h : NearState) (he : eraseP h = eraseP (hostOf ctx raw)) : NoPromises h :=
    ⟨eraseP_field he NearState.promises (fun _ => rfl),
      eraseP_field he NearState.returnedPromise (fun _ => rfl),
      eraseP_field he NearState.gasWeights (fun _ => rfl)⟩
  by_cases hok : c = .ok
  · have agrees (h h' : NearState) (he : eraseP h = eraseP (hostOf ctx raw))
        (hq : postDepOk ctx.protocol.fees.numExtraBytesRecord s reg h h') :
        AgreesWith (WNear.wnear cfg) ctx raw h' ((WNear.wnear cfg).step ctx (some s) .nearDeposit) :=
      agrees_success_deposit cfg ctx raw s hwf hs hraw h h' he ((cases_agree h he).trans hok)
        hl hn hU (effects h h' he hq)
    exact method_refines_callR (WNear.wnear cfg) size codeOf raw (some s) ctx .nearDeposit
      (preDepOk s reg) (costDep ctx.protocol s reg) (postDepOk ctx.protocol.fees.numExtraBytesRecord s reg)
      hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_234) funcType_234 (by decide) (by decide)
      (dep_runs ctx.protocol s reg)
      (fun hr => ⟨ctx.trie, depOk_initial ctx raw s hwf hraw hc hl hv hn hr, hok⟩)
      ⟨ctx.trie, depOk_unrecorded ctx raw s hwf hraw hc hl hv hn, (cases_agree _ rfl).trans hok⟩
      (fun e he => effects_noPromises (effects (erase (hostOf ctx raw)) e rfl he) (noPromises (erase (hostOf ctx raw)) rfl))
      (fun e he => effects_noPromises (effects (eraseP (hostOf ctx raw)) e rfl he) (noPromises (eraseP (hostOf ctx raw)) rfl))
      (fun e he => agrees (erase (hostOf ctx raw)) e rfl he)
      (fun e he => agrees (eraseP (hostOf ctx raw)) e rfl he) hbound
  · have agrees (h h' : NearState) (he : eraseP h = eraseP (hostOf ctx raw)) (hq : postDepP c h h') :
        AgreesPanic (WNear.wnear cfg) (utf8String c.text) h' ((WNear.wnear cfg).step ctx (some s) .nearDeposit) :=
      agreesPanic_deposit cfg ctx raw s hwf hs h he c (cases_agree h he) hok h'
        (postDepP_logs (eraseP_field he NearState.logs (fun _ => rfl)) hq)
    exact method_refines_callP (WNear.wnear cfg) size codeOf raw (some s) ctx .nearDeposit
      (preDepP s reg c) (costDep ctx.protocol s reg) (postDepP c) (utf8String c.text)
      hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_234) funcType_234 (by decide) (by decide)
      (dep_panics ctx.protocol s reg c hok)
      (fun hr => ⟨ctx.trie, depOk_initial ctx raw s hwf hraw hc hl hv hn hr, rfl⟩)
      ⟨ctx.trie, depOk_unrecorded ctx raw s hwf hraw hc hl hv hn, cases_agree _ rfl⟩
      (fun e he => postDepP_panicHost rfl he) (fun e he => postDepP_panicHost rfl he)
      (fun e he => agrees (erase (hostOf ctx raw)) e rfl he)
      (fun e he => agrees (eraseP (hostOf ctx raw)) e rfl he) hbound

end WNear.Binary.NearDepositMethod
