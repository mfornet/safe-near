import Skeleton.EmptyStorage
import Skeleton.SuccessExecution

/-!
# Actual successful empty-base writes at the receipt boundary

The storage frontier and post-storage resources are derived here, with original
credits, an explicit proof-size check and explicit ABI storage-usage room.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic NearInterface
open MeteredHosts MeteredHosts.StorageMetered

set_option maxHeartbeats 800000

private theorem frame_balance {before after : HostStore NearState} (h : StorageFrame.Frame before after) :
    after.host.context.accountBalance = before.host.context.accountBalance := by
  have hb := congrArg (fun ns : NearState => ns.context.accountBalance) h.2
  exact hb

theorem emptyAfter_logs (ctx : Context) (raw : Storage) : (emptyAfter ctx raw).host.logs = [] := by
  have hf := StorageFrame.Frame.logs (emptyAfter_frame ctx raw)
  exact hf.trans (storageInput_logs ctx.protocol (Near.Boundary.toVMContext ctx) raw)

theorem emptyAfter_promises (ctx : Context) (raw : Storage) : (emptyAfter ctx raw).host.promises = [] := by
  have hf := StorageFrame.Frame.promises (emptyAfter_frame ctx raw)
  exact hf.trans (storageInput_promises ctx.protocol (Near.Boundary.toVMContext ctx) raw)

theorem emptyAfter_balance (ctx : Context) (raw : Storage) :
    (emptyAfter ctx raw).host.context.accountBalance = ctx.balance + ctx.attached := by
  have hf := frame_balance (emptyAfter_frame ctx raw)
  exact hf.trans (storageInput_balance ctx.protocol (Near.Boundary.toVMContext ctx) raw)

theorem emptyAfter_config (ctx : Context) (raw : Storage) :
    (emptyAfter ctx raw).host.config = ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).config := by
  have hf := StorageFrame.Frame.config (emptyAfter_frame ctx raw)
  exact hf.trans (storageInput_config ctx.protocol (Near.Boundary.toVMContext ctx) raw)

theorem emptyAfter_extCosts (ctx : Context) (raw : Storage) :
    (emptyAfter ctx raw).host.extCosts = ctx.protocol.wasm.extCosts := by
  have hf := StorageFrame.Frame.extCosts (emptyAfter_frame ctx raw)
  exact hf.trans (storageInput_extCosts ctx.protocol (Near.Boundary.toVMContext ctx) raw)

private theorem finished_representation (extra : Nat) (before : HostStore NearState)
    (raw : RawStorage) (h : StorageRepresentation.Represents before.host raw) (key value : Near.Bytes) :
    let paid := (applyCharges (written before key value).host (postCharges before key)).1
    StorageRepresentation.Represents (finished extra before 1 0 u64Max 0 key value paid).host
      (rawWrite raw key value) := by
  have hw := (h.setStorage key value).invalidateIterators
  have hc := hw.applyCharges (postCharges before key) (postCharges_burnsOnly before key)
  exact hc.updateStorageUsage extra "storage_write" before before.mem (args 1 0 u64Max 0)

private theorem phases_representation (before : HostStore NearState) (prePaid triePaid : NearState)
    (trie : Near.TrieOverlay.State) (extra : Nat) (key value : Near.Bytes) (raw : RawStorage)
    (hr : StorageRepresentation.Represents prePaid raw) :
    let phase := prepared (Output.paidStore before prePaid) triePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    StorageRepresentation.Represents (finished extra phase 1 0 u64Max 0 key value paid).host
      (rawWrite raw key value) := by
  have hpre := hr.paidStore before
  have hphase := hpre.prepared (Output.paidStore before prePaid) triePaid trie
  exact finished_representation extra _ raw hphase key value

/-- The computed write retains key coverage as well as functional lookup. -/
theorem emptyAfter_representation (ctx : Context) (storage : Storage)
    (hwf : ctx.WF storage.toFinset) :
    StorageRepresentation.Represents (emptyAfter ctx storage).host
      (savedStorage storage ctx.args).toFinset := by
  have hp := (emptyBefore_representation ctx storage storage.toFinset hwf rfl).applyCharges
    (emptyPreCharges ctx storage) (StorageOverlay.preCharges_burnsOnly (emptyBefore ctx storage) 1 0 u64Max 0)
  rw [show (applyCharges (emptyBefore ctx storage).host (emptyPreCharges ctx storage)).1 = emptyPaid ctx storage
    by unfold emptyPaid; rfl] at hp
  have hf := phases_representation (emptyBefore ctx storage) (emptyPaid ctx storage)
    (applyCharges (accounted (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage)) ctx.trie).host
      (trieCharges ctx.trie ctx.trie)).1
    (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
      "k".toUTF8.toList) ctx.args) ctx.protocol.fees.numExtraBytesRecord "k".toUTF8.toList ctx.args storage.toFinset hp
  rw [show (savedStorage storage ctx.args).toFinset = rawWrite storage.toFinset "k".toUTF8.toList ctx.args
    from rawWrite_toFinset storage _ _]
  simpa only [emptyAfter, emptyPhase] using hf

private theorem charged_usage (before : NearState) (charges : List Charge)
    (h : ∀ c ∈ charges, BurnsOnly c) :
    (applyCharges before charges).1.context.storageUsage = before.context.storageUsage := by
  have hf := congrArg (fun ns : NearState => ns.context.storageUsage) (applyCharges_frame before charges h)
  exact hf

theorem emptyPaid_usage (ctx : Context) (raw : Storage) :
    (emptyPaid ctx raw).context.storageUsage = UInt64.ofNat ctx.storageUsage := by
  have hp := charged_usage (emptyBefore ctx raw).host (emptyPreCharges ctx raw)
    (StorageOverlay.preCharges_burnsOnly (emptyBefore ctx raw) 1 0 u64Max 0)
  rw [show (applyCharges (emptyBefore ctx raw).host (emptyPreCharges ctx raw)).1 = emptyPaid ctx raw
    by unfold emptyPaid; rfl] at hp
  exact hp.trans (storageInput_usage ctx.protocol (Near.Boundary.toVMContext ctx) raw)

/-- The phase's original cell is absent by canonical empty lookup and original
WF, rather than an assumed host-read equation. -/
theorem emptyPhase_writeUsage (ctx : Context) (storage : Storage)
    (hwf : ctx.WF storage.toFinset) (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none) :
    writeUsage ctx.protocol.fees.numExtraBytesRecord (emptyPhase ctx storage) "k".toUTF8.toList ctx.args =
      ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord := by
  have hn := StorageEmpty.storage_none (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage))
    ctx storage.toFinset hwf storage rfl (emptyPaid_store_represents ctx storage)
    "k".toUTF8.toList hentries hselected
  have hnone : (emptyPaid ctx storage).storage "k".toUTF8.toList = none := hn
  have hu : ctx.storageUsage < 2 ^ 64 := by have h := hwf.usage_room; omega
  simp only [writeUsage, emptyPhase, prepared, Output.paidStore, hnone, emptyPaid_usage,
    UInt64.toNat_ofNat_of_lt' hu]
  rw [show "k".toUTF8.toList.length = 1 by decide +kernel]

/-- Original protocol limits and frames supply every post-storage resource
needed by the proved body. The only storage check left as a premise is the
actual proof-size check on the staged trie. -/
theorem emptyAfter_resources (ctx : Context) (storage : Storage) (rest : Nat)
    (hwf : ctx.WF storage.toFinset) (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol storage).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) storage
        (emptyAfter ctx storage) (emptyCost ctx storage) rest))
    (hproof : recordedStorageError (emptyPaid ctx storage)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    SaveResources ctx.protocol (Near.Boundary.toVMContext ctx) storage
      (emptyAfter ctx storage) (emptyCost ctx storage) rest 0 := by
  have hf := emptyAfter_frame ctx storage
  refine ⟨?_, hf.1.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) storage),
    ?_, ?_, ?_, ?_, ?_, ?_, hcredits, ?_⟩
  · change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) ctx.args.length = true
    simpa [withinLimit] using hm.input
  · have hr := congrFun (StorageFrame.Frame.registers hf) 0
    exact hr.trans (storageInput_register ctx.protocol (Near.Boundary.toVMContext ctx) storage)
  · rw [emptyAfter_config]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthReturnedData) ctx.args.length = true
    simpa [withinLimit] using hm.returned
  · simp only [logCountError, emptyAfter_config, emptyAfter_logs]
    change (if 0 ≥ ctx.protocol.wasm.limits.maxNumberLogs then _ else none) = none
    simp only [Nat.not_le.mpr hm.logs, ↓reduceIte]
  · simp only [Wasm.Near.logSpace, emptyAfter_config, totalLogLength, emptyAfter_logs,
      List.map_nil, List.sum_nil]
    change 5 ≤ ctx.protocol.wasm.limits.maxTotalLogLength - 0
    simpa using hm.logBytes
  · rw [emptyAfter_extCosts]
    exact hread
  · intro limit hl
    have hc := congrArg NearConfig.maxLogLen (emptyAfter_config ctx storage)
    change (emptyAfter ctx storage).host.config.maxLogLen = some ctx.protocol.wasm.limits.maxTotalLogLength at hc
    rw [hc] at hl
    cases Option.some.inj hl
    simpa only [totalLogLength, emptyAfter_logs, List.map_nil, List.sum_nil, Nat.zero_add] using hm.logBytes
  · exact empty_storageFrontier_of_initialCredits ctx storage storage.toFinset rest hwf rfl
      hp.positive hm.key hm.value hentries hselected hcredits hproof

/-- Usage at the actual post-store equals the model's overhead-preserving
formula, with the u64 no-wrap obligation stated on original data. -/
theorem emptyAfter_usage (ctx : Context) (storage : Storage) (rest : Nat)
    (hwf : ctx.WF storage.toFinset) (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol storage).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) storage
        (emptyAfter ctx storage) (emptyCost ctx storage) rest))
    (hproof : recordedStorageError (emptyPaid ctx storage)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    (emptyAfter ctx storage).host.context.storageUsage.toNat =
      ctx.storageUsage - storageUsageOf ctx.protocol storage.toFinset +
        storageUsageOf ctx.protocol (savedStorage storage ctx.args).toFinset := by
  have hc := storageInput_credits ctx.protocol (Near.Boundary.toVMContext ctx) storage
    (emptyAfter ctx storage) (emptyCost ctx storage) rest hcredits
  have hi := empty_invoke ctx storage storage.toFinset _ hwf rfl hp.positive hm.key hm.value
    hentries hselected hc hproof
  have hu := hi.2.2.2.1
  rw [emptyPhase_writeUsage ctx storage hwf hentries hselected] at hu
  have hn := StorageEmpty.storage_none (emptyBefore ctx storage) ctx storage.toFinset hwf storage rfl
    (storageInput_represents ctx storage) "k".toUTF8.toList hentries hselected
  have hr := emptyBefore_representation ctx storage storage.toFinset hwf rfl
  have habsent : ∀ old, ("k".toUTF8.toList, old) ∉ storage.toFinset := by
    intro old hmem
    have he := (hr.lookup "k".toUTF8.toList old).mpr hmem
    rw [hn] at he
    cases he
  rw [hu]
  have hk : "k".toUTF8.toList.length = 1 := by decide +kernel
  have hu' := write_usage_fresh_toNat ctx.protocol storage.toFinset ctx.storageUsage "k".toUTF8.toList ctx.args
    hwf.usage_ge habsent (by simpa only [hk] using hroom)
  rw [show (savedStorage storage ctx.args).toFinset = rawWrite storage.toFinset "k".toUTF8.toList ctx.args
    from rawWrite_toFinset storage _ _]
  simpa only [hk] using hu'

/-- Actual receipt-level success for the empty canonical-base branch. Every
post-storage resource and the one storage invocation have been discharged;
remaining hypotheses concern original representation, protocol limits, credits,
usage width/stake and the explicit recorded-proof check. -/
theorem execOn_empty_matches_modelStep
    (gasBound : Context → Option Storage → Unit → Nat)
    (ctx : Context) (storage : Storage) (st : Option Storage) (rest : Nat)
    (hwf : ctx.WF storage.toFinset)
    (hrepresented : (model gasBound).Represents storage.toFinset st)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hstake : stakeDeficit ctx.protocol
      (ctx.storageUsage - storageUsageOf ctx.protocol storage.toFinset +
        storageUsageOf ctx.protocol (savedStorage storage ctx.args).toFinset)
      (ctx.balance + ctx.attached) ctx.locked = 0)
    (hcredits : ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol storage).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) storage
        (emptyAfter ctx storage) (emptyCost ctx storage) rest))
    (hproof : recordedStorageError (emptyPaid ctx storage)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    Matches (model gasBound) ctx storage.toFinset (Near.Boundary.execOn code storage ctx)
      ((model gasBound).step ctx st ()) := by
  have hr := emptyAfter_resources ctx storage rest hwf hp hm hread hentries hselected hcredits hproof
  have hu := emptyAfter_usage ctx storage rest hwf hp hm hentries hselected hroom hcredits hproof
  have hstate := represented_storage_getD gasBound storage st hrepresented
  have hupdated : (savedStorage (st.getD []) ctx.args).toFinset =
      (savedStorage storage ctx.args).toFinset := by
    simp only [savedStorage, rawWrite_toFinset, hstate]
  have hrep : StorageRepresentation.Represents (emptyAfter ctx storage).host
      (savedStorage (st.getD []) ctx.args).toFinset := by
    rw [hupdated]
    exact emptyAfter_representation ctx storage hwf
  have hpoststake : stakeDeficit ctx.protocol (emptyAfter ctx storage).host.context.storageUsage.toNat
      (emptyAfter ctx storage).host.context.accountBalance ctx.locked = 0 := by
    rw [hu, emptyAfter_balance]
    exact hstake
  apply execOn_matches_save_modelStep gasBound ctx storage st (emptyAfter ctx storage)
    (emptyCost ctx storage) rest 0 hmethod hp hr hm hrepresented hrep
    (emptyAfter_promises ctx storage) (emptyAfter_logs ctx storage) (emptyAfter_balance ctx storage) _ hpoststake
  rw [hupdated]
  exact hu

end WNear.Skeleton
