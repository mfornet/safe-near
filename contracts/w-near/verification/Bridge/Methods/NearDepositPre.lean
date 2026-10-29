import Bridge.Methods.NearDepositWords
import Bridge.Methods.NearDepositLogPre

/-!
# The initialized deposit's premises from the context

The storage proof budget fits the model's existing bound. All other fields of `DepOk`
follow from represented storage, `Context.WF`, and the protocol's cost and limit bounds.
The log-count lower bound remains explicit for the final protocol pinning step.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open Near.TrieOverlay
open WNear.Binary.FtTotalSupplyMethod (CostsV86 LimitsV86)

/-- All six bounded lookups and their value bytes fit the model's proof budget. -/
theorem budDep_le_proofBound (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) : budDep h ≤ WNear.proofBound ctx := by
  have hid : h.context.currentAccountId = ctx.current.bytes :=
    eraseP_field he (fun x => x.context.currentAccountId) fun _ => rfl
  have hp := predecessor_properties_of_eraseP ctx raw h he
  have hk : (DepositBody234.keyOf h).length ≤ 69 := by
    simp only [DepositBody234.keyOf, List.length_append, StateReadModel.accountsPrefix_length,
      bytes32, List.length_map, List.length_range]
    omega
  have keyBound (key : List UInt8) (hkey : key.length ≤ 69) :
      lookupProofBound (contractKey h.context.currentAccountId key) ≤
        lookupProofBoundLen (2 + ctx.current.bytes.length + WNear.maxStorageKeyBytes) := by
    apply FtTotalSupplyMethod.lookupProofBoundLen_mono
    rw [hid]
    simp only [contractKey, List.length_append, List.length_singleton, WNear.maxStorageKeyBytes,
      WNear.maxAccountIdBytes]
    omega
  have hstate := keyBound StateRead.stateKey (by decide)
  have haccount := keyBound (DepositBody234.keyOf h) hk
  simp only [budDep, WNear.proofBound, WNear.storageAccesses, WNear.maxStorageValueBytes,
    WNear.storageRemovals]
  omega

/-- Discharge the initialized method's host contract, given its recorded-proof room. -/
theorem depOk_of (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s)
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hv : 29 ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hn : 1 ≤ ctx.protocol.wasm.limits.maxNumberLogs) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (hproof : ProofBudget h ctx.trie (budDep h)) :
    DepOk h s ctx.trie (regOf s (.ofNear ctx.predecessor)) := by
  have hsto : h.storage = (hostOf ctx raw).storage := eraseP_field he NearState.storage fun _ => rfl
  have hcfg : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hid : h.context.currentAccountId = ctx.current.bytes :=
    eraseP_field he (fun x => x.context.currentAccountId) fun _ => rfl
  have hlim : ∀ (f : NearConfig → Option Nat) (n m : Nat), f (hostOf ctx raw).config = some m → n ≤ m →
      withinLimit (f h.config) n = true := by
    intro f n m hf hm
    rw [hcfg, hf]
    simpa only [withinLimit, decide_eq_true_eq] using hm
  have hkey := hl.storageKey
  have hreg := hl.register
  have hp := predecessor_properties_of_eraseP ctx raw h he
  have hs : InternalDepositOverflow.textSupply.length ≤ 16384 := by
    rw [DepositPanicsFull.textSup_length]; decide
  have ht : NearDepositPanics.textTooSmall.length ≤ 16384 := by
    rw [DepositPanicsFull.textSmall_length]; decide
  have hpText : NearDepositPanics.textPositive.length ≤ 16384 := by
    rw [DepositPanicsFull.textPos_length]; decide
  refine {
    value := ?_
    view := eraseP_field he (fun x => x.context.isView) fun _ => rfl
    acc := eraseP_field he NearState.storageAccounting fun _ => rfl
    canon := ⟨hwf.trie_canonical, hwf.trie_no_zero_hash⟩
    link := ?_
    proof := hproof
    lim5 := hlim NearConfig.maxStorageKeyLen 5 _ rfl (by omega)
    reg29 := hlim NearConfig.maxRegisterLen 29 _ rfl (by omega)
    vlim29 := hlim NearConfig.maxStorageValueLen 29 _ rfl hv
    valid := predecessor_valid_of_eraseP ctx raw h he
    limR := predecessor_register_fits ctx raw h he hl
    utf := hp.2.2
    ab := hp.2.1
    ab0 := by omega
    lim := predecessor_key_fits ctx raw h he hl
    vlim := hlim NearConfig.maxStorageValueLen 16 _ rfl (by omega)
    reg16 := hlim NearConfig.maxRegisterLen 16 _ rfl (by omega)
    store := regOf_storage ctx raw s hwf hraw h he
    log := deposit_log_ok ctx raw h he hl hc hn
    fit16 := initial_log_fits ctx raw h he hl 16 (by decide)
    ov16 := log_read_cost_fits ctx raw h he hc 16 (by decide)
    fitS := initial_log_fits ctx raw h he hl _ hs
    ovS := log_read_cost_fits ctx raw h he hc _ hs
    fitT := initial_log_fits ctx raw h he hl _ ht
    ovT := log_read_cost_fits ctx raw h he hc _ ht
    fitP := initial_log_fits ctx raw h he hl _ hpText
    ovP := log_read_cost_fits ctx raw h he hc _ hpText }
  · rw [hsto]
    apply FtTotalSupplyMethod.hostOf_storage_of_mem hwf
    rw [hraw]
    exact WNear.mem_encode_header.mpr rfl
  · intro key
    rw [hsto, hid]
    exact hostOf_storage_view ctx raw hwf key

/-- With the model's proof room, the actual initial host satisfies the complete contract. -/
theorem depOk_initial (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s)
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hv : 29 ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hn : 1 ≤ ctx.protocol.wasm.limits.maxNumberLogs) (hroom : ctx.ProofRoom (WNear.proofBound ctx)) :
    DepOk (erase (hostOf ctx raw)) s ctx.trie (regOf s (.ofNear ctx.predecessor)) := by
  apply depOk_of ctx raw s hwf hraw hc hl hv hn (erase (hostOf ctx raw)) rfl
  exact (FtTotalSupplyMethod.budget_of_room hwf hroom _ rfl rfl).mono
    (budDep_le_proofBound ctx raw _ rfl)

/-- The raised-resource comparison run records no proof and needs no proof-room premise. -/
theorem depOk_unrecorded (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s)
    (hc : CostsV86 ctx.protocol) (hl : LimitsV86 ctx.protocol)
    (hv : 29 ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hn : 1 ≤ ctx.protocol.wasm.limits.maxNumberLogs) :
    DepOk (eraseP (hostOf ctx raw)) s ctx.trie (regOf s (.ofNear ctx.predecessor)) := by
  apply depOk_of ctx raw s hwf hraw hc hl hv hn (eraseP (hostOf ctx raw)) rfl
  intro size hsize
  cases hsize

end WNear.Binary.NearDepositMethod
