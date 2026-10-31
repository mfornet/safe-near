import Bridge.Methods.FtBalanceOfObjectRun
import Bridge.Methods.FtBalanceOfObjectGas
import Bridge.Methods.FtBalanceOfCopiedPre

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_absent_refines_with_obligations (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (modelSt : Option WNear.State)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (tr : Near.TrieOverlay.State) (bud : Nat) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hlen : bs.length < 2 ^ 24) (hreceipt : bs.length ≤ 4194304)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
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
  have hbound := object_total_cost_le_model cfg ctx raw modelSt S a bs rest N size hc hsize hentry.2.input
    hlen hreceipt hnb ho hloop hentry.2.value hentry.2.absent
  exact method_refines_callR (WNear.wnear cfg) size codeOf raw modelSt ctx (.ftBalanceOf a)
    (CopiedAbsentPre S a bs tr bud) (objectMethodCost ctx.protocol S a bs rest N) (copiedMethodPost a tr)
    hp hwf (by rw [hm]; decide) (by rw [hm]; exact export_297) funcType_297 (by decide) (by decide)
    (object_absent_runs ctx.protocol S a bs rest N tr bud hlen hnb ho hloop hend )
    hentry.1 hentry.2
    (fun e he => copied_post_noPromises (e := erase (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    (fun e he => copied_post_noPromises (e := eraseP (hostOf ctx raw)) he ⟨rfl, rfl, rfl⟩)
    hag hagP (by simpa only [objectMethodCost, Nat.add_assoc] using hbound)

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_absent_refines_v86 (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (modelSt : Option WNear.State)
    (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (tr : Near.TrieOverlay.State) (bud : Nat) (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hlen : bs.length < 2 ^ 24) (hreceipt : bs.length ≤ 4194304)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hentry : CopiedEntryAt cfg ctx raw modelSt S a bs tr bud)
    (hrep : (WNear.wnear cfg).Represents raw modelSt) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx modelSt (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx modelSt (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx modelSt (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact object_absent_refines_with_obligations cfg size codeOf raw modelSt ctx S a bs rest N tr bud
    hp hwf hm hc hsize hlen hreceipt hnb ho hloop hend  hentry
    (copied_agreement_of_represents cfg ctx raw modelSt S a tr hrep hwf hentry.2.value hentry.2.absent _ rfl)
    (copied_agreement_of_represents cfg ctx raw modelSt S a tr hrep hwf hentry.2.value hentry.2.absent _ rfl)

end WNear.Binary.BalanceOf297AbsentCall

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open NearInterface ContractModel in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_absent_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol) (hsize : size ≤ 185625)
    (hlen : bs.length < 2 ^ 24) (hreceipt : bs.length ≤ 4194304)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (ha : a ∉ S.registered) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  obtain ⟨hinv, hraw⟩ := (show WNear.Inv cfg S ∧ raw = WNear.encode S from hrep)
  have hval : (hostOf ctx raw).storage WNear.stateKey = some (WNear.header S) :=
    FtTotalSupplyMethod.hostOf_storage_of_mem hwf (by rw [hraw]; exact Finset.mem_insert_self _ _)
  have hkey := NearDepositMethod.accountKey_ofNear a.toNear
  simp only [WNear.AccountId.ofNear_toNear] at hkey
  change WNear.accountKey a = WNear.accountsPrefix ++
    (bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList) at hkey
  rw [Wasm.ByteEncoding.string_utf8_length] at hkey
  have hnone : (hostOf ctx raw).storage (copiedKey a) = none := by
    have hr := FtBalanceOfMethod.reg_storage ctx raw S hwf hraw (hostOf ctx raw) rfl a
    rw [hkey] at hr
    simpa only [NearDepositMethod.regOf, if_neg ha, Option.map_none] using hr
  have hentry := copied_entry_at_of_ctx cfg ctx raw (some S) S a bs hwf hl hargs hlen hval hnone
  exact object_absent_refines_v86 cfg size codeOf raw (some S) ctx S a bs rest N ctx.trie
    (WNear.proofBound ctx) hp hwf hm hc hsize hlen hreceipt hnb ho hloop hend  hentry hrep

end WNear.Binary.BalanceOf297AbsentCall
