import Bridge.Methods.FtBalanceOfProviderRun
import Bridge.Methods.FtBalanceOfObjectAdequacy
import Bridge.Methods.FtBalanceOfCopiedRun

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

noncomputable def objectMethodCost (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (N : Nat) (e : NearState) : Nat :=
  11 * cfg.wasm.regularOpCost + objectBodyCost cfg.wasm e (inputHost e 0) S a bs rest N

theorem object_body_cost_erase (cfg : WasmConfig) (e : NearState) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (N : Nat) :
    objectBodyCost cfg (erase e) (inputHost (erase e) 0) S a bs rest N =
      objectBodyCost cfg e (inputHost e 0) S a bs rest N := rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_absent_runs (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (N : Nat) (st : Near.TrieOverlay.State) (bud : Nat)
    (hlen : bs.length < 2 ^ 24) (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
     :
    MethodRunsR cfg 297 (CopiedAbsentPre S a bs st bud) (objectMethodCost cfg S a bs rest N) (copiedMethodPost a st) := by
  have hpos : 0 < bs.length := by have := SerdeNextKey.getElem_lt ho; omega
  exact provider_absent_runs cfg S a bs (SerdeObjectNoEsc.parserCost cfg.wasm 1 bs rest N) 2 st bud
    hlen hpos (SerdeObjectNoEsc.deployed_parser_provider cfg bs rest a N hnb ho hloop hend)

end WNear.Binary.BalanceOf297AbsentCall
