import Bridge.Functions.BalanceOf297StateBridgeF
import NearLogic.Hosts.StorageWrite

/-! Derive the second-read frontier from a shared two-read proof budget. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.StateReadLen (LenStep)
open WNear.Binary.VecFromElem (roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.BalanceOfAbsent (code293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

/-- Remaining gas bound after the state read, independent of trie proof-budget propagation. -/
def BalanceReadGasAfterStateF (cfg : WasmConfig) (F : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (L : UInt32) (key : List UInt8) (K : Nat) : Prop :=
  ∀ h1, StorageReadPost h WNear.stateKey 0 st h1 →
    cost399None cfg (F + 1) 1 L h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) ≤ K

/-- The existing storage-read transition discharges the second lookup's trie and proof budget. -/
theorem balanceReadAfterState_of_budgetF (cfg : WasmConfig) (F : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (L : UInt32) (key : List UInt8) (K bud : Nat) (hcanon : Canon st) (hlink : StorageLink h st)
    (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key))) ≤ bud)
    (hlim : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 L ++ key)).length = true)
    (hnone : h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) = none)
    (hgas : BalanceReadGasAfterStateF cfg F h st L key K) :
    ∀ h1, StorageReadPost h WNear.stateKey 0 st h1 →
      ∃ st1 bud1, h1.storageAccounting = some st1 ∧
        withinLimit h1.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 L ++ key)).length = true ∧
        build st1.entries = .ok st1.base ∧ zeroHash ∉ st1.base.witness.map Prod.fst ∧
        h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) =
          viewVal st1 (contractKey h1.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key))) ∧
        ProofBudget h1 st1 bud1 ∧
        readProofCost (contractKey h1.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key)))
          (h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key))) ≤ bud1 ∧
        h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) = none ∧
        cost399None cfg (F + 1) 1 L h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) ≤ K := by
  intro h1 hread
  obtain ⟨st1, hacc1, hcanon1, hlink1, hp1, he1⟩ := StorageReadPost.next hread hcanon hlink hproof (by omega)
  have hstorage : h1.storage = h.storage :=
    (erase_field he1 NearState.storage (fun _ => rfl)).trans
      (storageReadRegs_field NearState.storage (fun _ _ _ => rfl) _ _ _)
  have hid : h1.context.currentAccountId = h.context.currentAccountId :=
    (erase_field he1 (fun x : NearState => x.context.currentAccountId) (fun _ => rfl)).trans
      (storageReadRegs_field (fun x : NearState => x.context.currentAccountId) (fun _ _ _ => rfl) _ _ _)
  have hcfg : h1.config = h.config :=
    (erase_field he1 NearState.config (fun _ => rfl)).trans
      (storageReadRegs_field NearState.config (fun _ _ _ => rfl) _ _ _)
  refine ⟨st1, bud - readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey),
    hacc1, ?_, hcanon1.1, hcanon1.2, hlink1 _, hp1, ?_, ?_, hgas h1 hread⟩
  · simpa [hcfg] using hlim
  · rw [hstorage, hid]
    omega
  · simpa [hstorage] using hnone

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The composed absent-account path with trie and proof budget propagated from the initial state. -/
theorem state_through_cleanup_of_budgetF (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R K : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
    (p c L idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hob : ob.length = 16) (holdState : oldState.length = 40) (holdContract : oldContract.length = 40)
    (hdest : dest.length = 16) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hr1 : roomFor len maxP 29)
    (hr2 : ∀ len1, len1 = len ∨ len1 = grownLen len 29 → roomFor len1 maxP 1)
    (hroom : ∀ len1, LenStep len 29 1 len1 → HeapRoomK 4 len1 maxP)
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 L ++ key)).length = true)
    (hnone : h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) = none)
    (hreg : withinLimit h.config.maxRegisterLen 29 = true) (hgas : BalanceReadGasAfterStateF cfg F h st L key K)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    stateCodeF e inst mi A n maxP mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (800 * cfg.regularOpCost + cost219F cfg F h S +
        (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + K +
          (17 * cfg.regularOpCost + cost96F cfg ((F + 1) + 3) 0 0 +
            (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h 3 + (660 * cfg.regularOpCost + R))))))) ∗
      pre219F n g ta A gt s (s + 88) idx maxP len ((p.toNat, c.toNat) :: live) F oldState h [.i32 (s + 88)] ∗
      n ↦[wms][ (s + 48).toNat ] oldContract ∗ n ↦[wms][ (s + 32).toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗
      n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ p.toNat + key.length ] rest ∗ n ↦[wms][ (s + 8).toNat ] ob ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n maxP hl live ((((F + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s x1 x2 (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 (s + 40)) [] ((f297.body.drop 68).take 82) Φ := by
  have hnext : BalanceReadAfterStateF cfg F h st L key K := balanceReadAfterState_of_budgetF cfg F h st L key K bud hcanon hlink hproof hbudget hlimAccount hnone hgas
  exact state_through_cleanup_absentF cfg lim d inst e mi A n g ta mx hm hd Cg R K gt s x1 x2 p c L idx maxP len live F hF
    key rest ob oldState oldContract dest out head hs hal hframe hkey hrest hc hL hp hob holdState holdContract hdest hout hhead
    h S st hv hr1 hr2 hroom hacc hlim hcanon.1 hcanon.2 (hlink _) (hproof.mono (by omega)) hreg hnext ptr0 hret Φ

end Spec

end WNear.Binary.BalanceOf297AbsentCall
