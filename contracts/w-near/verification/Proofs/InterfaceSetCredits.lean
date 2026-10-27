import Proofs.InterfaceSetTail
import Proofs.InterfaceSetHead
import Proofs.InterfaceBorrowAcquire

/-! Residual gas credits for the exact initialized setter phases. -/
namespace WNear.Proofs.InterfaceSetPhases
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetState
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

theorem savedArguments_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (11 * op + rest)) :
    (savedArguments s op p).host.gas.Credits rest := by
  have cr : (reserved s op p).host.gas.Credits (6 * op + rest) :=
    paid_credits s op 5 _ (hc.mono (by omega))
  exact InterfaceSetBody.twoWordsStore_credits (reserved s op p) op p.memoryIndex 20 16 rest
    (scratch p) p.vtable p.receiver p.memory cr

theorem arguments_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (50 * op + rest)) :
    (arguments s op p).host.gas.Credits rest := by
  have cs : (savedArguments s op p).host.gas.Credits (39 * op + rest) :=
    savedArguments_credits s op _ p (hc.mono (by omega))
  have cl : (lookupBefore s op p).host.gas.Credits (37 * op + rest) :=
    paid_credits (savedArguments s op p) op 2 _ (cs.mono (by omega))
  have ck : (looked s op p).host.gas.Credits (8 * op + rest) :=
    ValueReturnThreadLocal.indirectAfter_credits (lookupBefore s op p) op _ (cl.mono (by omega))
  have cg := paid_credits (looked s op p) op 3 (5 * op + rest) (ck.mono (by omega))
  exact paid_credits (paid (looked s op p) op 3) op 5 rest (cg.mono (by omega))

theorem acquired_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (121 * op + rest)) :
    (acquired s op p).host.gas.Credits rest := by
  have ca := arguments_credits s op (71 * op + rest) p (hc.mono (by omega))
  exact (InterfaceBorrow.calledAcquireStore_gas (arguments s op p) op p.globalIndex p.memoryIndex rest
    (scratch p) (scratch p + 8) 1074904 (savedMemory p) ca).2.2

theorem finalStore_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (222 * op + rest)) :
    (finalStore s op p).host.gas.Credits rest := by
  have ca := acquired_credits s op (101 * op + rest) p (hc.mono (by omega))
  have ci := InterfaceSetTail.installed_credits (acquired s op p) op (71 * op + rest) p
    (acquiredMemory p) (highMemory p) (lowMemory p) (ca.mono (by omega))
  have carg : (paid (installed s op p) op 5).host.gas.Credits (36 * op + (30 * op + rest)) :=
    paid_credits (installed s op p) op 5 _ (ci.mono (by omega))
  have cr := InterfaceBorrow.calledReleaseStore_credits (paid (installed s op p) op 5) op p.memoryIndex
    (30 * op + rest) (counter p) (installedMemory p) carg
  have cs := paid_credits (released s op p) op 2 (28 * op + rest) (cr.mono (by omega))
  have cb := StorePair.charged_credits (paid (released s op p) op 2) op (27 * op + rest) (cs.mono (by omega))
  have cget := paid_credits (branched s op p) op 1 (22 * op + (4 * op + rest)) (cb.mono (by omega))
  have cc := ValueReturnOuter.checkAfter_credits (paid (branched s op p) op 1) op p.globalIndex
    (4 * op + rest) (scratch p) cget
  exact paid_credits (ValueReturnOuter.checkAfter (paid (branched s op p) op 1) op p.globalIndex (scratch p)) op 4 rest cc

end WNear.Proofs.InterfaceSetPhases
