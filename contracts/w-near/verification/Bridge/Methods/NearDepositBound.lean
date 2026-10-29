import Bridge.Methods.NearDepositCostFees
import Bridge.Methods.NearDepositRefines
import Bridge.Methods.NearDepositUninit

/-!
# The model's gas bound covers initialized deposit

The bounded Wasm work and host fees fit `computeGas`. The two account mutations
and header write fit `trieGas`, and the boundary's read calls bill no trie nodes.
-/

namespace WNear.Binary.NearDepositGas

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary
open WNear.Binary.NearDepositMethod
open WNear.Binary.FtTotalSupplyMethod (CostsV86)
open Near.TrieOverlay

/-- Loading and every initialized deposit path fit the existing model bound. -/
theorem hbound_initialized (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s) (size : Nat)
    (hc : CostsV86 ctx.protocol) (hd : CostsDepositV86 ctx.protocol) (hsize : size ≤ 185625) :
    chargesUse (hostOf ctx raw) (loadingCharges size) +
      costDep ctx.protocol s (regOf s (.ofNear ctx.predecessor)) (erase (hostOf ctx raw)) ≤
        (WNear.wnear cfg).gas ctx (some s) .nearDeposit := by
  let h := erase (hostOf ctx raw)
  let reg := regOf s (.ofNear ctx.predecessor)
  let key := DepositBody234.keyOf h
  let n := (1 + (0 + 4 + UInt32.ofNat h.context.predecessorAccountId.length)).toNat
  have hp := predecessor_properties_of_eraseP ctx raw h rfl
  have ht : h.storageReadsFromTrie = false := rfl
  have hv : h.storage StateRead.stateKey = some (WNear.header s) := by
    rw [StateRead.stateKey_eq]
    exact FtTotalSupplyMethod.hostOf_storage_of_mem hwf (by rw [hraw]; exact WNear.mem_encode_header.mpr rfl)
  have hstore := regOf_storage ctx raw s hwf hraw h rfl
  have hb : ∀ v, h.storage key = some v → v.length ≤ 16 := by
    intro v hval
    rw [hstore] at hval
    cases hr : regOf s (.ofNear ctx.predecessor) with
    | none => rw [hr, Option.map_none] at hval; cases hval
    | some words =>
      rw [hr, Option.map_some] at hval
      cases hval
      simp
  have hn : n ≤ 69 := by simp [n]; omega
  have hk : key.length ≤ WNear.maxStorageKeyBytes := by
    simp only [key, DepositBody234.keyOf, List.length_append, StateReadModel.accountsPrefix_length,
      bytes32, List.length_map, List.length_range, WNear.maxStorageKeyBytes, WNear.maxAccountIdBytes]
    omega
  have hbody := body234_le ctx.protocol.wasm h s reg hp.2.1 ht hv hb
  have hhosts := methodHost_fees h key n hn hp.2.1
  have hfees := methodFees_le ctx raw hc hd
  change methodFees h ≤ 2000000000000 at hfees
  have htrie := trie_writes_le ctx raw key hk StateRead.stateKey rfl
  have hnPaths : 2 * ((2 * (contractKey h.context.currentAccountId key).length + 2) * trieNodeMax h) +
      (2 * (contractKey h.context.currentAccountId StateRead.stateKey).length + 2) * trieNodeMax h ≤
        WNear.trieGas ctx := by
    rw [← Nat.mul_assoc, ← Nat.add_mul]
    exact htrie
  change DepositBody234.cost234 ctx.protocol.wasm h s reg (DepositPanicsFull.kSup ctx.protocol.wasm)
    (DepositPanicsFull.kSmall ctx.protocol.wasm) (DepositPanicsFull.kPos ctx.protocol.wasm) ≤
      900000 * ctx.protocol.wasm.regularOpCost +
        54 * (ctx.protocol.wasm.linearOpBaseCost + ctx.protocol.wasm.linearOpUnitCost) + methodHost h key n at hbody
  erw [gas_234 cfg ctx (some s)]
  rw [NewMethod.loading_eq ctx raw size]
  simp only [costDep, costB, WNear.computeGas]
  have hload := Nat.mul_le_mul hc.loadingBytes hsize
  have hop := hc.regularOp
  have hlinB := hc.linearBase
  have hlinU := hc.linearUnit
  have hloadB := hc.loadingBase
  change _ + (9 * ctx.protocol.wasm.regularOpCost +
    DepositBody234.cost234 ctx.protocol.wasm h s reg (DepositPanicsFull.kSup ctx.protocol.wasm)
      (DepositPanicsFull.kSmall ctx.protocol.wasm) (DepositPanicsFull.kPos ctx.protocol.wasm)) ≤ _
  omega

end WNear.Binary.NearDepositGas
