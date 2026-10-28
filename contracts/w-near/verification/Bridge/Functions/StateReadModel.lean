import Bridge.Functions.StateRead
import Model.Storage

/-!
# `env::state_read` (219) on the model's state

`f219_spec` for a host whose storage at `STATE` is the model's `header s` (`Model/Storage.lean`:
borsh of the prefix `"a"`, `total_supply` as `u128`, `account_storage_usage` as `u64`, the value
`encode s` stores under `stateKey`). The `Contract` `state_read` leaves at `out` is
`contractBytes s p ++ pad`: the Borsh bytes of the supply and the usage, then the prefix `Vec`
`(p, 1, 1)`, `p` a fresh live block holding `"a"` (the layout of the harness's `stateRead`).
-/

namespace WNear.Binary.StateReadModel

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.BorshFT WNear.Binary.BorshContract WNear.Binary.StateRead
open WNear.Binary.StorageReadWrap (srCode costS)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.Interface (IfaceMod)

/-- The 36 bytes of the `Contract` for the model state `s`, its prefix buffer at `p`. -/
def contractBytes (s : WNear.State) (p : UInt32) : List UInt8 :=
  WNear.Borsh.u128 s.totalSupply ++ WNear.Borsh.u64 s.accountStorageUsage ++ bytes32 p ++ bytes32 1 ++ bytes32 1

theorem accountsPrefix_length : WNear.accountsPrefix.length = 1 := by decide +kernel

theorem header_eq (s : WNear.State) :
    WNear.header s = stateBytes (WNear.Borsh.u32 WNear.accountsPrefix.length) WNear.accountsPrefix
      ((WNear.Borsh.u128 s.totalSupply).take 8) ((WNear.Borsh.u128 s.totalSupply).drop 8)
      (WNear.Borsh.u64 s.accountStorageUsage) := by
  simp only [WNear.header, stateBytes, NearSdk.Borsh.bytes, List.append_assoc]
  rw [← List.append_assoc ((WNear.Borsh.u128 s.totalSupply).take 8), List.take_append_drop]

theorem ftHead_eq (s : WNear.State) (p : UInt32) :
    ftHead ((WNear.Borsh.u128 s.totalSupply).take 8) ((WNear.Borsh.u128 s.totalSupply).drop 8)
      (WNear.Borsh.u64 s.accountStorageUsage) p WNear.accountsPrefix = contractBytes s p := by
  simp only [ftHead, contractBytes, accountsPrefix_length]
  rw [List.take_append_drop]
  rfl

theorem decode_u32_prefix : Memory.decodeLE (WNear.Borsh.u32 WNear.accountsPrefix.length) =
    WNear.accountsPrefix.length := by decide +kernel

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- After `state_read` on the model state `s`: `contractBytes s p ++ pad` at `out`, `p` live holding
`"a"`, the value's buffer `pv` freed. -/
def postModel (n g ta : Nat) (A : Nat → Nat) (gt : GlobalType) (st : UInt32) (out : UInt32) (idx : UInt32)
    (maxP len : Nat) (live : List (Nat × Nat)) (s : WNear.State) (h : NearState) (Q : NearState → Prop)
    (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 st⟩ ∗ ifaceR n ta A ∗ stk n (st.toNat - 592) 592 ∗
    vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
    (∃ (pv p : UInt32) (pad : List UInt8) (len' : Nat), ⌜pad.length = 4⌝ ∗
      n ↦[wms][ out.toNat ] (contractBytes s p ++ pad) ∗
      heapInv n maxP len' (((p.toNat, 1) :: (pv.toNat, 29) :: live).erase (pv.toNat, 29)) 2 ∗
      n ↦[wms][ p.toNat ] WNear.accountsPrefix) ∗
    (∃ h', ⌜Q h'⌝ ∗ mhostPt h'))

theorem header_length (s : WNear.State) : (WNear.header s).length = 29 := by
  simp [WNear.header, NearSdk.Borsh.bytes, NearSdk.Borsh.u32, NearSdk.Borsh.u64, NearSdk.Borsh.u128,
    accountsPrefix_length]

set_option maxRecDepth 100000 in
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
/-- **`env::state_read::<Contract>`** (219) when the storage at `STATE` is the model's
`header s` (as in `encode s`): `Some(contract)` at `out`, the `Contract`'s bytes
`contractBytes s p` (the Borsh `u128` supply and `u64` usage, the prefix `Vec` `(p, 1, 1)`). -/
theorem f219_spec_model (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (e : Nat) (A : Nat → Nat)
    (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta) (hd : d + 17 < lim.maxCallDepth)
    (Cg : Nat) (gt : GlobalType) (sp out : UInt32) (hs : 592 ≤ sp.toNat) (hal : sp.toNat % 8 = 0)
    (hout : out.toNat + 40 ≤ 2 ^ 32) (idx : UInt32) (maxP len : Nat)
    (live : List (Nat × Nat)) (ob : List UInt8) (hob : ob.length = 40) (h : NearState) (s : WNear.State)
    (hv : h.storage WNear.stateKey = some (WNear.header s))
    (hroom1 : roomFor len maxP 29)
    (hroom2 : ∀ len', len' = len ∨ len' = grownLen len 29 → roomFor len' maxP 1)
    (st : Near.TrieOverlay.State)
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hp : ∀ x ∈ st.prospective, x.1 ≠ contractKey h.context.currentAccountId WNear.stateKey)
    (hcm : ∀ x ∈ st.committed, x.1 ≠ contractKey h.context.currentAccountId WNear.stateKey)
    (hlink : h.storage WNear.stateKey =
      (st.entries.find? (·.1 == contractKey h.context.currentAccountId WNear.stateKey)).map (·.2))
    (hproof : ProofBudget h st (lookupProofBound (contractKey h.context.currentAccountId WNear.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true) :
    stateCode e inst mi A n maxP mx
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f219 Cg
        (pre219 n g ta A gt sp out idx maxP len live ob h)
        (fun _ => 105 * cfg.regularOpCost +
          (40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5) +
            costS cfg h (some (WNear.header s))) +
          cost161 cfg 1 + 726 * cfg.regularOpCost + 334 * cfg.regularOpCost)
        (postModel n g ta A gt sp out idx maxP len live s h (StorageReadPost h StateRead.stateKey 0 st)) := by
  rw [← stateKey_eq] at hv hp hcm hlink hproof
  have hl := header_length s
  have e := f219_spec (GF := GF) cfg lim d type htype inst mi e A n g ta mx hm hd Cg gt sp out hs hal hout idx
    maxP len live ob hob h (WNear.Borsh.u32 WNear.accountsPrefix.length) WNear.accountsPrefix
    ((WNear.Borsh.u128 s.totalSupply).take 8) ((WNear.Borsh.u128 s.totalSupply).drop 8)
    (WNear.Borsh.u64 s.accountStorageUsage) (by simp [NearSdk.Borsh.u32])
    (by simp [NearSdk.Borsh.u128]) (by simp [NearSdk.Borsh.u128]) (by simp [NearSdk.Borsh.u64])
    decode_u32_prefix (by rw [accountsPrefix_length]; decide) (by rw [← header_eq]; exact hv)
    (by rw [← header_eq, hl]; decide) (by rw [← header_eq, hl]; exact hroom1)
    (by rw [← header_eq, hl, accountsPrefix_length]; exact hroom2) st hacc hlim hb hz hp hcm hlink hproof
    (by rw [← header_eq, hl]; exact hreg)
  rw [← header_eq, accountsPrefix_length] at e
  have hpost : post219 (GF := GF) n g ta A gt sp out idx maxP len live WNear.accountsPrefix
      ((WNear.Borsh.u128 s.totalSupply).take 8) ((WNear.Borsh.u128 s.totalSupply).drop 8)
      (WNear.Borsh.u64 s.accountStorageUsage) (WNear.header s).length h (StorageReadPost h StateRead.stateKey 0 st) =
      postModel n g ta A gt sp out idx maxP len live s h (StorageReadPost h StateRead.stateKey 0 st) := by
    funext args rs
    simp only [post219, postModel, ftHead_eq, hl, accountsPrefix_length]
  rw [hpost] at e
  exact e

end Spec

end WNear.Binary.StateReadModel
