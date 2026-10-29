import Bridge.Methods.NearDepositWords

/-!
# Initialized deposit panics agree with the model

The four failing branches preserve the logs and report exactly the model's panic.
These are the agreement obligations of `method_refines_callP`; the successful mint
is handled by a separate agreement proof.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near NearLogic NearInterface
open WNear.Binary.DepositBody
open WNear.Binary.NewBody (keep Keep)

/-- The model panic associated with a failing branch; the `ok` value is unused. -/
def casePanic : DCase → WNear.Panic
  | .pos => .requiresPositiveDeposit
  | .small => .depositTooSmall
  | .bal => .balanceOverflow
  | .sup => .totalSupplyOverflow
  | .ok => .requiresPositiveDeposit

theorem caseResult_panic (c : DCase) (hc : c ≠ .ok) (s : WNear.State) (env : WNear.Env) :
    caseResult c s env = .error (casePanic c) := by
  cases c <;> first | rfl | exact False.elim (hc rfl)

theorem casePanic_logs (c : DCase) : (casePanic c).logs = [] := by
  cases c <;> rfl

/-- The exact Rust panic-hook text (or direct SDK panic) is the model's message. -/
theorem casePanic_text (c : DCase) (hc : c ≠ .ok) :
    utf8String c.text = (casePanic c).message := by
  cases c with
  | pos => exact NearDepositPanics.utf8String_textPositive
  | small => exact NearDepositPanics.utf8String_textTooSmall
  | bal => exact InternalDepositOverflow.balMsg_utf8String
  | sup => exact NearDepositPanics.utf8String_textSupply
  | ok => exact False.elim (hc rfl)

/-- A failed initialized deposit passes through the boundary with its panic and no logs. -/
theorem step_deposit_panic (cfg : WNear.Config) (ctx : Context) (s : WNear.State)
    (p : WNear.Panic) (hp : WNear.nearDeposit s (.ofContext ctx) = .error p) (hl : p.logs = []) :
    (WNear.wnear cfg).step ctx (some s) .nearDeposit =
      .error { failure := .panic p, logs := [] } := by
  show WNear.contractStep ctx (some s) .nearDeposit = _
  have hs : WNear.step (.ofRuntime ctx.protocol) (some s) (.ofContext ctx) .nearDeposit = .error p := hp
  rw [WNear.contractStep, hs]
  simp only [WNear.stepLogs, hl]
  rfl

/-- A host satisfying the binary panic postcondition reports no execution issue. -/
theorem postDepP_panicHost {c : DCase} {e e' : NearState} (hi : e.lastExecutionIssue = none)
    (hp : postDepP c e e') : PanicHost (utf8String c.text) e' := by
  obtain ⟨h, hk, rfl⟩ := hp
  exact ⟨rfl, (congrArg Keep.issue hk).trans hi⟩

theorem postDepP_logs {c : DCase} {e e' : NearState} (hl : e.logs = [])
    (hp : postDepP c e e') : logsOf e' = [] := by
  obtain ⟨h, hk, rfl⟩ := hp
  have hh : h.logs = [] := (congrArg Keep.logs hk).trans hl
  show h.logs.map _ = []
  rw [hh]
  rfl

/-- The initialized panic's final host agrees with the model result on the same branch. -/
theorem agreesPanic_deposit (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (c : DCase)
    (hcase : caseDep h s (regOf s (.ofNear ctx.predecessor)) = c) (hc : c ≠ .ok)
    (e : NearState) (hl : logsOf e = []) :
    AgreesPanic (WNear.wnear cfg) (utf8String c.text) e ((WNear.wnear cfg).step ctx (some s) .nearDeposit) := by
  have hm := model_eq_caseDep ctx raw s hwf hs h he
  rw [hcase, caseResult_panic c hc] at hm
  refine ⟨_, step_deposit_panic cfg ctx s (casePanic c) hm (casePanic_logs c), ?_, hl.symm⟩
  change (casePanic c).failure = .panic (utf8String c.text)
  rw [casePanic_text c hc]
  cases c <;> rfl

end WNear.Binary.NearDepositMethod
