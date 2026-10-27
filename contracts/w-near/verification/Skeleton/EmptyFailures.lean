import Skeleton.SuccessCost
import Skeleton.LogFailure
import Skeleton.LogLengthFailure

/-!
# Empty-base failures from original boundary data

Storage's local frontier is derived from the original well-formed trie and
one context-only gas bound. Output failures do not require successful return
lengths, storage-usage room, or a zero storage-stake deficit.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts

/-- Count rejection needs only a prefix of the ordinary execution budget. -/
theorem logFailureAttemptBudget_le_executionBudget (ctx : Context) (raw : Storage)
    (post : HostStore NearState) (storageCost rest : Nat) :
    logFailureAttemptBudget ctx raw post storageCost rest ≤
      executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest := by
  have hb : logFailureCost post ≤ burnSum
      (successLogBefore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post).host.extCosts savedCharges := by
    change post.host.extCosts.cost "base" ≤ burnSum post.host.extCosts savedCharges
    simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]
  rw [logFailureAttemptBudget_eq, executionBudget_eq]
  omega

/-- Actual count rejection on an empty base, with no intermediate storage
execution or credits premise. The write is performed and then rolled back. -/
theorem execOn_empty_matches_log_zero
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hwf : ctx.WF raw.toFinset)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hzero : ctx.protocol.wasm.limits.maxNumberLogs = 0)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  have hc := emptyCredits_of_gasLimit_allReturn ctx raw 0 hp.positive hkey hvalue
    (by simpa only [Nat.add_zero] using hgas)
  have hs := empty_storageFrontier_of_initialCredits ctx raw raw.toFinset 0 hwf rfl
    hp.positive hkey hvalue hentries hselected hc hproof
  exact execOn_matches_log_zero gasBound ctx raw st (emptyAfter ctx raw) (emptyCost ctx raw) 0 0
    hmethod hp hinput hkey hvalue hzero hs (emptyAfter_frame ctx raw)
    (hc.mono (logFailureAttemptBudget_le_executionBudget ctx raw _ _ _))

/-- Log-length rejection needs only a prefix of the ordinary execution budget. -/
theorem logLengthFailureAttemptBudget_le_executionBudget (ctx : Context) (raw : Storage)
    (post : HostStore NearState) (storageCost rest : Nat) :
    logLengthFailureAttemptBudget ctx raw post storageCost rest ≤
      executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw post storageCost rest := by
  have hb : logLengthFailureCost post ≤ burnSum
      (successLogBefore ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) post).host.extCosts savedCharges := by
    change post.host.extCosts.cost "base" + post.host.extCosts.cost "utf8_decoding_base" ≤
      burnSum post.host.extCosts savedCharges
    simp [savedCharges, savedReadCharges, extCharges, ext1, burnSum, burnCost]
  rw [logLengthFailureAttemptBudget_eq, executionBudget_eq]
  omega

/-- Actual log-length rejection on an empty base, with no intermediate storage
execution or credits premise. The write is performed and then rolled back. -/
theorem execOn_empty_matches_log_length
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hwf : ctx.WF raw.toFinset)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hshort : ctx.protocol.wasm.limits.maxTotalLogLength < 5)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  have hc := emptyCredits_of_gasLimit_allReturn ctx raw 0 hp.positive hkey hvalue
    (by simpa only [Nat.add_zero] using hgas)
  have hs := empty_storageFrontier_of_initialCredits ctx raw raw.toFinset 0 hwf rfl
    hp.positive hkey hvalue hentries hselected hc hproof
  exact execOn_matches_log_length gasBound ctx raw st (emptyAfter ctx raw) (emptyCost ctx raw) 0 0
    hmethod hp hinput hkey hvalue hcount hshort hs (emptyAfter_frame ctx raw)
    (hc.mono (logLengthFailureAttemptBudget_le_executionBudget ctx raw _ _ _))

end WNear.Skeleton
