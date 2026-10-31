import Bridge.Methods.FtBalanceOfModelGas
import Bridge.Methods.FtBalanceOfAbsentCompose
import Bridge.Methods.FtTotalSupplyPre
/-! The copied-array absent case through the metered run and conditional receipt-boundary composition. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

/-- The two read keys used by the copied-array absent-account body. -/
abbrev copiedKey (a : WNear.AccountId) : List UInt8 :=
  WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)

/-- The remaining host/trie premises at a method's erased initial host. -/
structure CopiedAbsentPre (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
    (st : Near.TrieOverlay.State) (bud : Nat) (e : NearState) : Prop where
  input : e.context.input = bs
  inputLimit : withinLimit e.config.maxRegisterLen bs.length = true
  value : e.storage WNear.stateKey = some (WNear.header S)
  accounting : e.storageAccounting = some st
  keyLimit : withinLimit e.config.maxStorageKeyLen 5 = true
  canonical : Canon st
  link : StorageLink e st
  proof : ProofBudget e st bud
  budget : readProofCost (contractKey e.context.currentAccountId WNear.stateKey) (e.storage WNear.stateKey) +
    readProofCost (contractKey e.context.currentAccountId (copiedKey a)) (e.storage (copiedKey a)) ≤ bud
  accountLimit : withinLimit e.config.maxStorageKeyLen (copiedKey a).length = true
  absent : e.storage (copiedKey a) = none
  registerLimit : withinLimit e.config.maxRegisterLen 29 = true
  returnLimit : withinLimit e.config.maxReturnLen 3 = true

noncomputable def copiedMethodCost (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (j k : Nat) (e : NearState) : Nat :=
  11 * cfg.wasm.regularOpCost + initialBodyCost cfg.wasm e (inputHost e 0) S a bs rest j k

def copiedMethodPost (a : WNear.AccountId) (st : Near.TrieOverlay.State) (e e' : NearState) : Prop :=
  ∃ h1 st1 h2, StorageReadPost (inputHost e 0) WNear.stateKey 0 st h1 ∧
    StorageReadPost h1 (copiedKey a) 0 st1 h2 ∧ e' = erase (h2.selectReturnValue [34, 48, 34])

theorem initial_body_cost_erase (cfg : WasmConfig) (e : NearState) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (j k : Nat) :
    initialBodyCost cfg (erase e) (inputHost (erase e) 0) S a bs rest j k =
      initialBodyCost cfg e (inputHost e 0) S a bs rest j k := rfl

theorem storage_read_post_erase_source (h : NearState) (key : List UInt8) (r : UInt64)
    (st : Near.TrieOverlay.State) (h' : NearState) :
    StorageReadPost (erase h) key r st h' ↔ StorageReadPost h key r st h' := by
  unfold StorageReadPost
  simp only [erase_storageReadRegs]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem copied_array_absent_runs (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (j k : Nat) (st : Near.TrieOverlay.State) (bud : Nat)
    (hlen : bs.length < 2 ^ 24) (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hcopied : ¬ borrowed (bs.drop (j + 1))) :
    MethodRunsR cfg 297 (CopiedAbsentPre S a bs st bud) (copiedMethodCost cfg S a bs rest j k) (copiedMethodPost a st) := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 297)) (entryCost cfg.wasm (.next (startW cfg h 297))) =
      (.next { startW cfg h 297 with store := wStore cfg (charged h (11 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_297, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [copiedMethodCost] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1)
      (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have hp : CopiedAbsentPre S a bs st bud (charged h (11 * cfg.wasm.regularOpCost)) :=
    ⟨hpre.input, hpre.inputLimit, hpre.value, hpre.accounting, hpre.keyLimit, hpre.canonical,
      hpre.link, hpre.proof, hpre.budget, hpre.accountLimit, hpre.absent, hpre.registerLimit, hpre.returnLimit⟩
  have hbody : (charged h (11 * cfg.wasm.regularOpCost)).gas.used +
      initialBodyCost cfg.wasm (charged h (11 * cfg.wasm.regularOpCost))
        (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) S a bs rest j k ≤ Cg := by
    rw [charged_gas_used, ← initial_body_cost_erase, erase_charged]
    simp only [copiedMethodCost] at hcost
    omega
  have had := copied_array_absent_adequate cfg Cg a bs rest j k hlen ho hj hq he hk hend hmodel hcopied
    (charged h (11 * cfg.wasm.regularOpCost)) (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0)
    hp.input rfl hp.inputLimit S st hp.value hp.accounting hp.keyLimit hp.canonical hp.link bud hp.proof
    hp.budget hp.accountLimit hp.absent hp.registerLimit hp.returnLimit hbody
    (by simpa [charged] using hC1) (by simpa [charged] using hC2)
  rw [← startW_thread297 cfg h] at had
  have hending := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := FtTotalSupplyMethod.runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hending
  obtain ⟨rfl, cs, hcs, hlk⟩ := hending
  have hrun := FtTotalSupplyMethod.done_of_values (FtTotalSupplyMethod.runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨h1, st1, h2, hs1, hs2, heq, hu⟩ := endCells297_ends hcs hlk
  have heinput : erase (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) = erase (inputHost (erase h) 0) :=
    erase_inputHost (by rw [erase_charged, erase_erase]) 0
  have hs1' : StorageReadPost (inputHost (erase h) 0) WNear.stateKey 0 st h1 := by
    apply (storage_read_post_erase_source _ _ _ _ _).mp
    have hr := (storage_read_post_erase_source _ _ _ _ _).mpr hs1
    rwa [heinput] at hr
  exact ⟨σ.store, hrun, ⟨h1, st1, h2, hs1', hs2, heq⟩, hu⟩

theorem storage_read_post_field {α : Type} (f : NearState → α) (hf : ∀ x, f (erase x) = f x)
    (hreg : ∀ x i v, f (x.setRegister i v) = f x) (hacc : ∀ x a, f { x with storageAccounting := a } = f x)
    {h h' : NearState} {key : List UInt8} {r : UInt64} {tr : Near.TrieOverlay.State}
    (hp : StorageReadPost h key r tr h') : f h' = f h := by
  obtain ⟨s2, _, _, he⟩ := hp
  rw [erase_field he f hf]
  unfold storageReadRegs
  split
  · split
    · exact hacc _ _
    · rw [hreg]; exact hacc _ _
  · exact hacc _ _

theorem copied_post_field {α : Type} (f : NearState → α) (hf : ∀ x, f (erase x) = f x)
    (hsel : ∀ x b, f (x.selectReturnValue b) = f x) (hreg : ∀ x i v, f (x.setRegister i v) = f x)
    (hacc : ∀ x a, f { x with storageAccounting := a } = f x)
    {a : WNear.AccountId} {tr : Near.TrieOverlay.State} {e e' : NearState}
    (hp : copiedMethodPost a tr e e') : f e' = f e := by
  obtain ⟨h1, st1, h2, hs1, hs2, rfl⟩ := hp
  rw [hf, hsel, storage_read_post_field f hf hreg hacc hs2, storage_read_post_field f hf hreg hacc hs1]
  unfold inputHost
  split
  · rfl
  · exact hreg _ _ _

theorem copied_post_noPromises {a : WNear.AccountId} {tr : Near.TrieOverlay.State} {e e' : NearState}
    (hp : copiedMethodPost a tr e e') (hn : NoPromises e) : NoPromises e' := by
  have hpr := copied_post_field NearState.promises (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ => rfl) hp
  have hgw := copied_post_field NearState.gasWeights (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ => rfl) hp
  refine ⟨hpr.trans hn.promises, ?_, hgw.trans hn.weights⟩
  obtain ⟨h1, st1, h2, _, _, rfl⟩ := hp
  rfl

/-- Remaining caller obligation: instantiate the concrete host/trie precondition with and without recorded proof. -/
def CopiedEntryAt (cfg : WNear.Config) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (modelSt : Option WNear.State) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
    (tr : Near.TrieOverlay.State) (bud : Nat) : Prop :=
  (ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
    CopiedAbsentPre S a bs tr bud (erase (hostOf ctx raw))) ∧
    CopiedAbsentPre S a bs tr bud (eraseP (hostOf ctx raw))

/-- Remaining caller obligation: the actual two-read/zero-return postcondition agrees with the model. -/
def CopiedAgreement (cfg : WNear.Config) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (modelSt : Option WNear.State) (a : WNear.AccountId) (tr : Near.TrieOverlay.State) (e0 : NearState) : Prop :=
  ∀ e, copiedMethodPost a tr e0 e →
    AgreesWith (WNear.wnear cfg) ctx raw e ((WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a))

theorem funcType_297 : wNearModule.funcType? 297 = some { params := [], results := [] } := by kernel_rfl

theorem export_297 : wNearModule.exportFunc? "ft_balance_of" = some 297 := by decide

open NearInterface ContractModel in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem copied_array_absent_refines_with_obligations (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (modelSt : Option WNear.State)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat)
    (tr : Near.TrieOverlay.State) (bud : Nat) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hlen : bs.length < 2 ^ 24) (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length))]? = some 0x5D)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hentry : CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
    (hag : CopiedAgreement cfg ctx raw modelSt a tr (erase (hostOf ctx raw)))
    (hagP : CopiedAgreement cfg ctx raw modelSt a tr (eraseP (hostOf ctx raw))) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  have hbound := initial_total_cost_le_model cfg ctx raw modelSt S a bs rest j k size hc hsize hentry.2.input
    hlen hj hq hk hend hmodel hentry.2.value hentry.2.absent
  exact method_refines_callR (WNear.wnear cfg) size codeOf raw modelSt ctx (.ftBalanceOf a)
    (CopiedAbsentPre S a bs tr bud) (copiedMethodCost ctx.protocol S a bs rest j k) (copiedMethodPost a tr)
    hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_297) funcType_297 (by decide) (by decide)
    (copied_array_absent_runs ctx.protocol S a bs rest j k tr bud hlen ho hj hq he hk hend hmodel hcopied)
    hentry.1 hentry.2
    (fun e he => copied_post_noPromises (e := erase (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    (fun e he => copied_post_noPromises (e := eraseP (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    hag hagP (by simpa only [copiedMethodCost, Nat.add_assoc] using hbound)
end WNear.Binary.BalanceOf297AbsentCall
