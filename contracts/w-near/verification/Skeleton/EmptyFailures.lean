import Skeleton.SuccessCost
import Skeleton.LogFailure
import Skeleton.LogLengthFailure
import Skeleton.ReturnLengthFailure
import Skeleton.FailureCosts

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

/-- Returned-data rejection retains the saved log and rolls back the write,
with storage and checked-cost room derived from original data. -/
theorem execOn_empty_matches_return_length
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hwf : ctx.WF raw.toFinset)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hinput : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hcount : 0 < ctx.protocol.wasm.limits.maxNumberLogs)
    (hloglen : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength)
    (hshort : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length)
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
  exact execOn_matches_return_length gasBound ctx raw st (emptyAfter ctx raw) (emptyCost ctx raw) 0 0
    hmethod hp hinput hkey hvalue hcount hloglen hshort
    (saveEmptyCost_read_room ctx raw.toFinset hwf hgas) hs (emptyAfter_frame ctx raw) hc

/-- One sufficient-gas matching theorem for every resource-limit branch of
the empty-base slice, including either final storage-stake outcome. This does
not assume that any input, key, value, log or return limit accepts. -/
theorem execOn_empty_matches_modelStep_allLimits
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (raw : Storage) (st : Option Storage)
    (hwf : ctx.WF raw.toFinset)
    (hrepresented : (model gasBound).Represents raw.toFinset st)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx raw)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx raw).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx raw.toFinset (Near.Boundary.execOn code raw ctx)
      ((model gasBound).step ctx st ()) := by
  by_cases hpre : ctx.protocol.wasm.limits.maxRegisterSize < ctx.args.length ∨
      ctx.protocol.wasm.limits.maxLengthStorageKey < 1 ∨
      ctx.protocol.wasm.limits.maxLengthStorageValue < ctx.args.length
  · exact execOn_matches_preStorageFailure gasBound ctx raw st hmethod hp hpre hgas
  have hi : ctx.args.length ≤ ctx.protocol.wasm.limits.maxRegisterSize := by omega
  have hk : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey := by omega
  have hv : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue := by omega
  by_cases hz : ctx.protocol.wasm.limits.maxNumberLogs = 0
  · exact execOn_empty_matches_log_zero gasBound ctx raw st hwf hmethod hp hi hk hv hz
      hentries hselected hgas hproof
  have hn : 0 < ctx.protocol.wasm.limits.maxNumberLogs := Nat.pos_of_ne_zero hz
  by_cases hl : ctx.protocol.wasm.limits.maxTotalLogLength < 5
  · exact execOn_empty_matches_log_length gasBound ctx raw st hwf hmethod hp hi hk hv hn hl
      hentries hselected hgas hproof
  have hlog : 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength := Nat.le_of_not_gt hl
  by_cases hr : ctx.protocol.wasm.limits.maxLengthReturnedData < ctx.args.length
  · exact execOn_empty_matches_return_length gasBound ctx raw st hwf hmethod hp hi hk hv hn hlog hr
      hentries hselected hgas hproof
  have hm : ModelSaveLimits ctx := ⟨hi, hk, hv, hn, hlog, Nat.le_of_not_gt hr⟩
  exact (execOn_empty_matches_and_gas gasBound ctx raw st hwf hrepresented hmethod hp hm
    hentries hselected hroom hgas hproof).1

end WNear.Skeleton
