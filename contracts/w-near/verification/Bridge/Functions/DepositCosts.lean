import Bridge.Functions.DepositSegAll

/-!
# The costs of `near_deposit`'s calls, from the host 232 starts on (M8)

The callees' specifications state their costs on the host each call starts from. 232 reaches
`internal_deposit` through `predecessor_account_id` (a register), `contains_key` (the
accounting) and, on a new account, the write of its record. What the costs read of a host is
kept by all of them (`keep`: the fee tables, the account, whether reads walk the trie) but the
stored values: `costSegAll_congr` restates the segment's cost on any host with the same `keep`
and the same storage.
-/

namespace WNear.Binary.DepositCosts

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary
open WNear.Binary.NewBody (Keep keep SameCost sameCost_of_keep chargesUse_congr trieNodeMax_congr storageWriteUse_congr)
open WNear.Binary.DepositSeg (costSeg costTail_congr cost401s_congr)
open WNear.Binary.DepositSegAll (costSegAll)
open WNear.Binary.InternalDepositOverflow (cost406bal cost406sup panicUtf8Use_congr)

theorem readNodes_congr {x y : NearState} (hk : keep x = keep y) (k : List UInt8) :
    readNodes x k = readNodes y k := by
  have : x.storageReadsFromTrie = y.storageReadsFromTrie := congrArg Keep.fromTrie hk
  simp only [readNodes, this]

theorem storageReadUse_congr {x y : NearState} (hk : keep x = keep y) {k : List UInt8}
    (hs : x.storage k = y.storage k) (a : Nat) : storageReadUse x k a = storageReadUse y k a := by
  have h := sameCost_of_keep hk
  have hc := chargesUse_congr h
  simp only [storageReadUse, storageReadPhaseUse, hc, trieNodeMax_congr h, readNodes_congr hk, hs, h.2.2]

theorem storageHasKeyUse_congr {x y : NearState} (hk : keep x = keep y) (k : List UInt8) (a : Nat) :
    storageHasKeyUse x k a = storageHasKeyUse y k a := by
  have h := sameCost_of_keep hk
  have hc := chargesUse_congr h
  simp only [storageHasKeyUse, hc, trieNodeMax_congr h, readNodes_congr hk, h.2.2]

theorem costSF_congr (cfg : WasmConfig) (F : Nat) {x y : NearState} (h : SameCost x y) (b : List UInt8) :
    StorageReadWrapF.costSF cfg F x b = StorageReadWrapF.costSF cfg F y b := by
  have hc := chargesUse_congr (h.setRegister 0 b)
  have hr : ∀ z : NearState, (z.setRegister 0 b).registers 0 = some b := by
    intro z; simp [NearState.setRegister]
  simp only [StorageReadWrapF.costSF, ReadRegisterF.cost523F, registerLenUse, hc, UInt64.toNat_zero, hr,
    ReadRegisterF.costRestF, readRegisterUse]

theorem cost405_congr (cfg : WasmConfig) (F : Nat) (pl L : UInt32) {x y : NearState} (hk : keep x = keep y)
    {k : List UInt8} (hs : x.storage k = y.storage k) (b : List UInt8) :
    InternalDeposit.cost405 cfg F pl L x k b = InternalDeposit.cost405 cfg F pl L y k b := by
  simp only [InternalDeposit.cost405, LookupMapGet.cost399, storageReadUse_congr hk hs,
    costSF_congr cfg F (sameCost_of_keep hk)]

theorem cost394_congr (cfg : WasmConfig) (F : Nat) (pl L : UInt32) {x y : NearState} (hk : keep x = keep y)
    (k : List UInt8) :
    LookupMapContains.cost394 cfg F pl L x k = LookupMapContains.cost394 cfg F pl L y k := by
  simp only [LookupMapContains.cost394, LookupMapContains.cost396, storageHasKeyUse_congr hk]

theorem costSegAll_congr (cfg : WasmConfig) (F : Nat) (pl L : UInt32) {x y : NearState} (hk : keep x = keep y)
    {k : List UInt8} (hs : x.storage k = y.storage k) (x0 x1 t0 t1 lo hi : UInt64) (ab : List UInt8)
    (K879 : Nat → Keep → Nat) :
    costSegAll cfg F pl L x k x0 x1 t0 t1 lo hi ab K879 = costSegAll cfg F pl L y k x0 x1 t0 t1 lo hi ab K879 := by
  have h := sameCost_of_keep hk
  simp only [costSegAll, costSeg, cost406bal, cost406sup, cost405_congr cfg _ pl L hk hs,
    cost401s_congr cfg _ pl L h hs, costTail_congr cfg _ lo hi ab h, panicUtf8Use_congr h, hk]

end WNear.Binary.DepositCosts
