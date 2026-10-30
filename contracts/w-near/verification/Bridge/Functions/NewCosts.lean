import Bridge.Functions.ContractNew

/-!
# The costs of `new`'s success path, from the host it starts on

The specifications of `Contract::new` (289) and `state_write` (220) state their costs on the host
each call starts from, which `new` reaches only through the storage calls before it. Those costs
read nothing of the host but its fee tables, its account and the stored value of the key they
touch (`SameCost`): `chargesUse_congr`, `storageWriteUse_congr`, `cost404_congr`, `cost402_congr`.

`k2New`: the bound `f289_spec` asks of the removal side of `measure_account_storage_usage`, on
the host with the dummy record written (`withDummy`).
-/

namespace WNear.Binary.NewBody

open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary
open WNear.Binary.LookupMapOps (cost401 cost402)
open WNear.Binary.MeasureUsage (mKey mVal cost404)
open WNear.Binary.StorageWrite (evictedRegister)

/-- What the costs read of a host: the fee tables and the account. -/
def SameCost (x y : NearState) : Prop :=
  x.extCosts = y.extCosts ∧ x.fees = y.fees ∧ x.context.currentAccountId = y.context.currentAccountId

theorem SameCost.refl (x : NearState) : SameCost x x := ⟨rfl, rfl, rfl⟩

theorem SameCost.symm {x y : NearState} (h : SameCost x y) : SameCost y x := ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

theorem SameCost.trans {x y z : NearState} (h1 : SameCost x y) (h2 : SameCost y z) : SameCost x z :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem SameCost.of_erase {x y : NearState} (he : erase x = erase y) : SameCost x y :=
  ⟨erase_field he NearState.extCosts fun _ => rfl, erase_field he NearState.fees fun _ => rfl,
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl⟩

theorem chargesUse_congr {x y : NearState} (h : SameCost x y) (cs : List Charge) :
    chargesUse x cs = chargesUse y cs := by
  unfold chargesUse
  congr 1
  apply List.map_congr_left
  intro c _
  cases c <;> simp [chargeUse, h.1, h.2.1]

theorem trieNodeMax_congr {x y : NearState} (h : SameCost x y) : trieNodeMax x = trieNodeMax y := by
  simp [trieNodeMax, h.1]

theorem storageWriteUse_congr {x y : NearState} (h : SameCost x y) {k : List UInt8}
    (hk : x.storage k = y.storage k) (a b : Nat) : storageWriteUse x k a b = storageWriteUse y k a b := by
  have hc := chargesUse_congr h
  simp only [storageWriteUse, storageWritePhaseUse, hc, trieNodeMax_congr h, hk, h.2.2]

theorem storageRemoveUse_congr {x y : NearState} (h : SameCost x y) {k : List UInt8}
    (hk : x.storage k = y.storage k) (a : Nat) : storageRemoveUse x k a = storageRemoveUse y k a := by
  have hc := chargesUse_congr h
  simp only [storageRemoveUse, storageRemovePhaseUse, hc, trieNodeMax_congr h, hk, h.2.2]

theorem storageUsageUse_congr {x y : NearState} (h : SameCost x y) : storageUsageUse x = storageUsageUse y :=
  chargesUse_congr h _

theorem cost404_congr (cfg : WasmConfig) (F : Nat) {x y : NearState} (h : SameCost x y)
    (hk : x.storage mKey = y.storage mKey) (K2 : Nat) : cost404 cfg F x K2 = cost404 cfg F y K2 := by
  simp only [cost404, cost401, storageUsageUse_congr h, storageWriteUse_congr h hk]

theorem SameCost.setRegister {x y : NearState} (h : SameCost x y) (i : Nat) (v : List UInt8) :
    SameCost (x.setRegister i v) (y.setRegister i v) := h

theorem cost402_congr (cfg : WasmConfig) (F : Nat) (pl L : UInt32) {x y : NearState} (h : SameCost x y)
    {k : List UInt8} (hk : x.storage k = y.storage k) (b : List UInt8) :
    cost402 cfg F pl L x k b = cost402 cfg F pl L y k b := by
  have hc := chargesUse_congr (h.setRegister evictedRegister.toNat b)
  have hr : ∀ z : NearState, (z.setRegister evictedRegister.toNat b).registers evictedRegister.toNat = some b := by
    intro z; simp [NearState.setRegister]
  simp only [cost402, storageRemoveUse_congr h hk, ReadRegisterF.cost523F, registerLenUse, hc, hr,
    ReadRegisterF.costRestF, readRegisterUse]

/-- The host with the dummy record written. -/
def withDummy (h : NearState) : NearState := { h with storage := fun k => if k = mKey then some mVal else h.storage k }

/-- The bound on the removal side of `measure_account_storage_usage` (`f289_spec`'s `K2`). -/
def k2New (cfg : WasmConfig) (h : NearState) : Nat :=
  250 * cfg.regularOpCost + storageUsageUse h + cost402 cfg 4 1 64 (withDummy h) mKey mVal

theorem k2New_bound (cfg : WasmConfig) (h h1 : NearState) (hs : SameCost h1 h) (hk : h1.storage mKey = some mVal) :
    250 * cfg.regularOpCost + storageUsageUse h1 + cost402 cfg (1 + 3) 1 64 h1 mKey mVal ≤ k2New cfg h := by
  have e1 := storageUsageUse_congr hs
  have e2 := cost402_congr cfg 4 1 64 (x := h1) (y := withDummy h) hs (k := mKey) (by simp [withDummy, hk]) mVal
  simp only [k2New, show 1 + 3 = 4 from rfl, e1, e2, le_refl]

end WNear.Binary.NewBody
