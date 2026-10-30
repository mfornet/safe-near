import Architect
import Architect.CollectUsed
import Proofs.Refinement
import Bridge.Functions.SerdeIgnClosing
import Bridge.Functions.SerdeIgnMemberBudget
import Bridge.Functions.SerdeStructObjModelState
import Bridge.Functions.FromSliceEsc
import Bridge.Functions.FromSliceSpec
import Bridge.Methods.FtBalanceOfModel
import Bridge.Functions.StorageReadNoneF
import Bridge.Functions.LookupMapGetNone

/-! The browsable proof frontier. Definitions marked Open state contracts, not proofs. -/

attribute [blueprint "frontier:exported"
  (title := /-- All exported runtime clauses -/)
  (statement := /-- All exported runtime clauses. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.refines_wnear_exported

attribute [blueprint "frontier:dispatch"
  (title := /-- Checked dispatch over all 15 methods -/)
  (statement := /-- Checked dispatch over all 15 methods. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.Exported.all_methods

attribute [blueprint "frontier:remaining"
  (title := /-- Nine remaining full method contracts -/)
  (statement := /-- Nine remaining full method contracts. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.Exported.Remaining

attribute [blueprint "frontier:binary-size"
  (title := /-- Embedded deployed code size -/)
  (statement := /-- Embedded deployed code size. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.deployed_code_size

attribute [blueprint "frontier:protocol-runtime"
  (title := /-- Pinned protocol: runtime -/)
  (statement := /-- Pinned protocol: runtime. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_runtime_obligation

attribute [blueprint "frontier:protocol-costs"
  (title := /-- Pinned protocol: costs -/)
  (statement := /-- Pinned protocol: costs. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_costs_obligation

attribute [blueprint "frontier:protocol-limits"
  (title := /-- Pinned protocol: limits -/)
  (statement := /-- Pinned protocol: limits. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_limits_obligation

attribute [blueprint "frontier:protocol-new_costs"
  (title := /-- Pinned protocol: new costs -/)
  (statement := /-- Pinned protocol: new costs. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_new_costs_obligation

attribute [blueprint "frontier:protocol-deposit_costs"
  (title := /-- Pinned protocol: deposit costs -/)
  (statement := /-- Pinned protocol: deposit costs. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.pinned_deposit_costs_obligation

attribute [blueprint "frontier:method-ft_total_supply"
  (title := /-- ft\_total\_supply -/)
  (statement := /-- ft\_total\_supply. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.ftTotalSupply_complete

attribute [blueprint "frontier:method-storage_minimum_balance"
  (title := /-- storage\_minimum\_balance -/)
  (statement := /-- storage\_minimum\_balance. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.storageMinimumBalance_complete

attribute [blueprint "frontier:method-storage_balance_bounds"
  (title := /-- storage\_balance\_bounds -/)
  (statement := /-- storage\_balance\_bounds. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.storageBalanceBounds_complete

attribute [blueprint "frontier:method-ft_metadata"
  (title := /-- ft\_metadata -/)
  (statement := /-- ft\_metadata. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.ftMetadata_complete

attribute [blueprint "frontier:method-new"
  (title := /-- new -/)
  (statement := /-- new. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.new_complete

attribute [blueprint "frontier:method-near_deposit"
  (title := /-- near\_deposit -/)
  (statement := /-- near\_deposit. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.Exported.nearDeposit_complete

attribute [blueprint "frontier:method-near_withdraw"
  (title := /-- near\_withdraw -/)
  (statement := /-- near\_withdraw. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.nearWithdraw_obligation

attribute [blueprint "frontier:method-ft_transfer"
  (title := /-- ft\_transfer -/)
  (statement := /-- ft\_transfer. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.ftTransfer_obligation

attribute [blueprint "frontier:method-ft_transfer_call"
  (title := /-- ft\_transfer\_call -/)
  (statement := /-- ft\_transfer\_call. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.ftTransferCall_obligation

attribute [blueprint "frontier:method-ft_balance_of"
  (title := /-- ft\_balance\_of -/)
  (statement := /-- ft\_balance\_of. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.ftBalanceOf_obligation

attribute [blueprint "frontier:method-ft_resolve_transfer"
  (title := /-- ft\_resolve\_transfer -/)
  (statement := /-- ft\_resolve\_transfer. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.ftResolveTransfer_obligation

attribute [blueprint "frontier:method-storage_deposit"
  (title := /-- storage\_deposit -/)
  (statement := /-- storage\_deposit. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.storageDeposit_obligation

attribute [blueprint "frontier:method-storage_withdraw"
  (title := /-- storage\_withdraw -/)
  (statement := /-- storage\_withdraw. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.storageWithdraw_obligation

attribute [blueprint "frontier:method-storage_unregister"
  (title := /-- storage\_unregister -/)
  (statement := /-- storage\_unregister. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.storageUnregister_obligation

attribute [blueprint "frontier:method-storage_balance_of"
  (title := /-- storage\_balance\_of -/)
  (statement := /-- storage\_balance\_of. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.storageBalanceOf_obligation

attribute [blueprint "frontier:ignore-hyp"
  (title := /-- Full ignored-reader interface -/)
  (statement := /-- Full ignored-reader interface. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjState.IgnoreHyp

attribute [blueprint "frontier:key-conditions"
  (title := /-- Uniform reachable key bounds -/)
  (statement := /-- Uniform reachable key bounds. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjKeyState.KeyConditions

attribute [blueprint "frontier:value-conditions"
  (title := /-- Uniform reachable value bounds -/)
  (statement := /-- Uniform reachable value bounds. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjValueState.ValueConditions

attribute [blueprint "frontier:accept-parser"
  (title := /-- Uniform accepting argument contract -/)
  (statement := /-- Uniform accepting argument contract. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.FromSliceSpec.AcceptContract

attribute [blueprint "frontier:reject-parser"
  (title := /-- Uniform rejecting argument contract -/)
  (statement := /-- Uniform rejecting argument contract. Open verification obligation; its statement exists but is not discharged. -/)
  (notReady := true)]
  WNear.Binary.FromSliceSpec.RejectContract

attribute [blueprint "frontier:object-parser"
  (title := /-- Changing-state object parser -/)
  (statement := /-- Changing-state object parser. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.SerdeStructObjModelState.f228_obj_model

attribute [blueprint "frontier:array-parser"
  (title := /-- Copied/escaped array parser wrapper -/)
  (statement := /-- Copied/escaped array parser wrapper. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.FromSliceEsc.f65_arr_okAt

attribute [blueprint "frontier:ignored-opening"
  (title := /-- Complete funded ignored-container opening -/)
  (statement := /-- Complete funded ignored-container opening. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.SerdeIgnOpening.entry_funded

attribute [blueprint "frontier:ignored-closing"
  (title := /-- Complete funded nested close -/)
  (statement := /-- Complete funded nested close. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnClosing.funded_nonempty

attribute [blueprint "frontier:ignored-last-close"
  (title := /-- Complete funded final close -/)
  (statement := /-- Complete funded final close. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnClosing.funded_empty

attribute [blueprint "frontier:ignored-first"
  (title := /-- Complete funded first-member iteration -/)
  (statement := /-- Complete funded first-member iteration. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnMemberBudget.first_funded

attribute [blueprint "frontier:ignored-comma"
  (title := /-- Complete funded comma iteration -/)
  (statement := /-- Complete funded comma iteration. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnMemberBudget.comma_funded

attribute [blueprint "frontier:ignored-member"
  (title := /-- Funded array/key/colon tail -/)
  (statement := /-- Funded array/key/colon tail. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnMemberBudget.next_funded

attribute [blueprint "frontier:ignored-scalar"
  (title := /-- Complete scalar dispatch -/)
  (statement := /-- Complete scalar dispatch. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnScalar.scalar

attribute [blueprint "frontier:ignored-depth"
  (title := /-- Logical depth bounded by consumed bytes -/)
  (statement := /-- Logical depth bounded by consumed bytes. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnProgress.run_consumed

attribute [blueprint "frontier:ignored-reserve"
  (title := /-- Closing-byte reserve accounting -/)
  (statement := /-- Closing-byte reserve accounting. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.SerdeIgnBudget.regular_reserve

attribute [blueprint "frontier:storage"
  (title := /-- Actual storage-read host contract -/)
  (statement := /-- Actual storage-read host contract. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)
  (notReady := true)]
  WNear.Binary.StorageReadWrap.f548_spec_host

attribute [blueprint "frontier:runtime-boundary"
  (title := /-- Runtime and rollback composition -/)
  (statement := /-- Runtime and rollback composition. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.method_boundary

attribute [blueprint "frontier:runtime-call"
  (title := /-- Per-call runtime refinement -/)
  (statement := /-- Per-call runtime refinement. Kernel status, reviewed premises, unresolved dependencies and caller integration are checked by the frontier exporter. -/)]
  WNear.Binary.method_refines_call

attribute [blueprint "frontier:scratch-room"
  (title := /-- Reachable scratch growth room -/)
  (statement := /-- Open verification obligation: derive this explicit allocation-room premise on all reachable states. -/)
  (notReady := true)]
  WNear.Binary.ScratchGrow.roomRes

attribute [blueprint "frontier:string-room"
  (title := /-- Reachable escaped-string growth room -/)
  (statement := /-- Open verification obligation: derive this explicit allocation-room premise on all reachable states. -/)
  (notReady := true)]
  WNear.Binary.ParseStr.roomRun

attribute [blueprint "frontier:owned-room"
  (title := /-- Reachable owned-string allocation room -/)
  (statement := /-- Open verification obligation: derive this explicit allocation-room premise on all reachable states. -/)
  (notReady := true)]
  WNear.Binary.VecFromElem.roomFor

attribute [blueprint "frontier:protocol-available"
  (title := /-- Pinned protocol parses successfully -/)
  (statement := /-- Open obligation: prove that the pinned protocol JSON actually parses before instantiating the deployed theorem. -/)
  (notReady := true)]
  WNear.PinnedProtocolAvailable

attribute [blueprint "frontier:ft-balance-model"
  (title := /-- Balance lookup and model boundary agreement -/)
  (statement := /-- For an arbitrary requested account, represented storage and decoded balance agree with the initialized model boundary result, including missing accounts and the storage-stake failure. Wasm execution and parsing remain open. -/)]
  WNear.Binary.FtBalanceOfMethod.account_lookup_and_step

attribute [blueprint "frontier:storage-read-absent"
  (title := /-- Absent storage read with allocator and trie accounting -/)
  (statement := /-- The actual storage-read wrapper returns None for an absent key and preserves the allocator bound under the metered host and trie-proof premises. Its LookupMap callers remain to be integrated. -/)]
  WNear.Binary.StorageReadWrapF.f548_noneF_host

attribute [blueprint "frontier:lookup-raw-absent"
  (title := /-- Absent LookupMap raw read -/)
  (statement := /-- The actual get_raw function constructs the storage key, executes the absent read and frees its temporary key; the reachable allocator-room obligation remains open. -/)
  (notReady := true)]
  WNear.Binary.LookupMapGet.f400_none
