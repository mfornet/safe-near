import Bridge.Methods.AcceptedInputBounds
import Bridge.Methods.FtBalanceOfFullWeightedObject
import Bridge.Functions.BalanceOf297ArrayParser
import Bridge.Functions.SerdeWeightedTraceCost
import Bridge.Functions.BalanceOf297PresentFamily
import Bridge.Methods.FtBalanceOfProviderLinearGas

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary
open WNear.Binary.BalanceOf297AbsentCall
open WNear.Binary.U128From (u128Bytes)

theorem vec16_cost_le (cfg : WasmConfig) :
    VecFromElem.cost687 cfg 0 16 ≤ 1600 * cfg.regularOpCost +
      cfg.linearOpBaseCost + cfg.linearOpUnitCost := by
  have hc := FtTotalSupplyMethod.c581 cfg 16 (by decide)
  simp only [VecFromElem.cost687, FtTotalSupplyMethod.and0, ite_true,
    VecFromElem.costAlloc, AllocZeroed.cost153,
    show MemSet.cost (16 : UInt32).toNat = 214 by rfl]
  omega

theorem present_storage_register64_cost_le (cfg : WasmConfig) (F : Nat) (h : NearState)
    (lo hi : UInt64) (hF : F ≤ 64) :
    StorageReadWrapF.costSF cfg F h (u128Bytes lo hi) ≤
      25000 * cfg.regularOpCost + cfg.linearOpBaseCost + cfg.linearOpUnitCost +
      registerLenUse h + readRegisterUse h 16 := by
  have hd := storage_register64_delta cfg F h (u128Bytes lo hi) hF
  have hv := vec16_cost_le cfg
  change VecFromElem.cost687 cfg 0 (UInt32.ofNat 16) ≤ 1600 * cfg.regularOpCost +
    cfg.linearOpBaseCost + cfg.linearOpUnitCost at hv
  have hbytes : (u128Bytes lo hi).length = 16 := by simp [u128Bytes, storeBytes]
  simp only [StorageReadWrap.costS, ReadRegister.costRest, hbytes] at hd
  omega

theorem present_lookup64_cost_le (cfg : WasmConfig) (F : Nat) (L : UInt32) (h : NearState)
    (key : List UInt8) (lo hi : UInt64) (hF : F ≤ 64) (hL : L.toNat ≤ 64) :
    LookupMapGet.cost399 cfg F 1 L h key (u128Bytes lo hi) ≤
      90000 * cfg.regularOpCost + 3 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
      storageReadUse h key (5 + L.toNat) + registerLenUse h + readRegisterUse h 16 := by
  have hn := lookup_none64_cost_le cfg F L h key hF hL
  have hs := present_storage_register64_cost_le cfg F h lo hi hF
  simp only [LookupMapGet.cost399None, LookupMapGet.cost399] at hn ⊢
  omega

theorem present_suffix64_cost_le (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64)
    (hF : F ≤ 44) : presentParserSuccessCost cfg F h S a lo hi 0 ≤
      250000 * cfg.regularOpCost + 7 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
      NearLogic.storageReadUse h StateRead.stateKey 5 + NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 +
      NearLogic.storageReadUse h (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (5 + a.val.utf8ByteSize) +
      NearLogic.registerLenUse h + NearLogic.readRegisterUse h 16 +
      NearLogic.valueReturnUse h (resultLen lo hi).toNat := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hn : a.val.utf8ByteSize ≤ 64 := by
    rw [← Wasm.ByteEncoding.string_utf8_length]; exact hvalid.1.2
  have hsize : (UInt32.ofNat a.val.utf8ByteSize).toNat = a.val.utf8ByteSize := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hs := state_read64_cost_le cfg (F + 1) h S (by omega)
  have hl := present_lookup64_cost_le cfg (F + 2) (UInt32.ofNat a.val.utf8ByteSize) h
    (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) lo hi (by omega) (by omega)
  have hr := return64_cost_le cfg (F + 6) lo hi (by omega)
  rw [hsize] at hl
  simp only [presentParserSuccessCost, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  omega



noncomputable def presentProviderBodyCost (cfg : WasmConfig) (h0 h : NearState) (S : WNear.State) (a : WNear.AccountId)
    (lo hi : UInt64) (parseGas outF : Nat) : Nat :=
  475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + EnvInput.cost527 cfg h0 +
    (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
      parseGas + presentParserSuccessCost cfg outF h S a lo hi 0)))))


def presentBodyHostUse (h0 h : NearState) (a : WNear.AccountId) (bs : List UInt8) (lo hi : UInt64) : Nat :=
  NearLogic.inputUse h0 + NearLogic.registerLenUse (NearLogic.inputHost h0 0) +
    NearLogic.readRegisterUse (NearLogic.inputHost h0 0) bs.length +
    NearLogic.storageReadUse h StateRead.stateKey 5 + NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 +
    NearLogic.storageReadUse h (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (5 + a.val.utf8ByteSize) +
    NearLogic.registerLenUse h + NearLogic.readRegisterUse h 16 +
    NearLogic.valueReturnUse h (resultLen lo hi).toNat


theorem present_provider_body_linear_cost (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h0 h : NearState) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8) (parseGas outF : Nat)
    (hinput : h0.context.input = bs) (hlen : bs.length < 2 ^ 24) (hF : outF ≤ 44)
    (hparse : parseGas ≤ 1000000000000 + (2215 + 470 * bs.length) * p.wasm.regularOpCost) :
    presentProviderBodyCost p.wasm h0 h S a lo hi parseGas outF ≤
      1300 * 10 ^ 9 + 397500000 * bs.length + presentBodyHostUse h0 h a bs lo hi := by
  have hinputCost := input_cost_le p.wasm h0 bs hinput hlen
  have hs := present_suffix64_cost_le p.wasm outF h S a lo hi hF
  have hcst := Nat.mul_le_mul_left 270000 hc.regularOp
  have hbase := Nat.mul_le_mul_left 9 hc.linearBase
  have hunit := Nat.mul_le_mul_left 265 hc.linearUnit
  have hlin : 483 * p.wasm.regularOpCost ≤ 397500000 := by have := hc.regularOp; omega
  have hlinear := Nat.mul_le_mul_right bs.length hlin
  have hcombine : 470 * bs.length * p.wasm.regularOpCost + 13 * bs.length * p.wasm.regularOpCost =
      483 * bs.length * p.wasm.regularOpCost := by ring
  simp only [presentProviderBodyCost, presentBodyHostUse]
  simp only [Nat.mul_add, Nat.mul_left_comm, Nat.mul_comm] at hparse hinputCost hlinear hcombine ⊢
  omega

/-- The final observable host and gas cells of the copied-array absent-account run. -/
def presentEndCells297 (Cg : Nat) (h : NearState) (a : WNear.AccountId) (lo hi : UInt64) (st : Near.TrieOverlay.State)
    (cs : List (Loc × Cell NearState)) : Prop :=
  ∃ (h1 : NearState) (st1 : Near.TrieOverlay.State) (h2 : NearState)
      (g : Near.GasCounter) (p : Near.GasProfile) (act : List (String × Nat)),
    StorageReadPost h WNear.stateKey 0 st h1 ∧
    StorageReadPost h1 (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2 ∧
    cs = [(Loc.host, .host (erase (h2.selectReturnValue ([34] ++ FmtDigits.decDigits (FmtU128.val lo hi) ++ [34])))),
      (gasLoc, gasCellOf g p act)] ∧ g.used ≤ Cg

theorem presentEndCells297_ends {Cg : Nat} {h : NearState} {a : WNear.AccountId} {lo hi : UInt64}
    {st : Near.TrieOverlay.State} {σ' : MStore} {cs : List (Loc × Cell NearState)}
    (hc : presentEndCells297 Cg h a lo hi st cs) (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    ∃ h1 st1 h2, StorageReadPost h WNear.stateKey 0 st h1 ∧
      StorageReadPost h1 (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2 ∧
      erase σ'.store.host = erase (h2.selectReturnValue ([34] ++ FmtDigits.decDigits (FmtU128.val lo hi) ++ [34])) ∧ σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h1, st1, h2, g, p, act, hs1, hs2, rfl, hg⟩ := hc
  have hh := hl _ List.mem_cons_self
  have hg' := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at hh hg'
  obtain ⟨hgg, -, -⟩ := gasCellOf_inj hg'
  exact ⟨h1, st1, h2, hs1, hs2, hh, hgg ▸ hg⟩

end WNear.Binary.BalanceOf297PresentCall

/-! Actual-code parser providers, whole-method resource composition and receipt refinement.
The general provider and model-budget obligations remain explicit. -/
