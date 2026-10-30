import Bridge.Functions.BalanceOf297ReadBudget

/-! The state read preserves the subsequent balance lookup's gas bound. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateRead (stateCode pre219)
open WNear.Binary.StateReadLen (LenStep)
open WNear.Binary.VecFromElem (roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.BalanceOfAbsent (code293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.FtTotalSupply (cost219)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

/-- A storage read preserves the cost bound for a later read of any key. -/
theorem storageReadUse_after_read {h h1 : NearState} {st : Near.TrieOverlay.State}
    {first next : List UInt8} {r : UInt64} (hread : StorageReadPost h first r st h1) (n : Nat) :
    storageReadUse h1 next n = storageReadUse h next n := by
  obtain ⟨st1, _, _, he⟩ := hread
  have hf : h1.fees = h.fees :=
    (erase_field he NearState.fees (fun _ => rfl)).trans
      (storageReadRegs_field NearState.fees (fun _ _ _ => rfl) _ _ _)
  have hx : h1.extCosts = h.extCosts :=
    (erase_field he NearState.extCosts (fun _ => rfl)).trans
      (storageReadRegs_field NearState.extCosts (fun _ _ _ => rfl) _ _ _)
  have hs : h1.storage = h.storage :=
    (erase_field he NearState.storage (fun _ => rfl)).trans
      (storageReadRegs_field NearState.storage (fun _ _ _ => rfl) _ _ _)
  have hi : h1.context.currentAccountId = h.context.currentAccountId :=
    (erase_field he (fun x : NearState => x.context.currentAccountId) (fun _ => rfl)).trans
      (storageReadRegs_field (fun x : NearState => x.context.currentAccountId) (fun _ _ _ => rfl) _ _ _)
  have ht : h1.storageReadsFromTrie = h.storageReadsFromTrie :=
    (erase_field he NearState.storageReadsFromTrie (fun _ => rfl)).trans
      (storageReadRegs_field NearState.storageReadsFromTrie (fun _ _ _ => rfl) _ _ _)
  unfold storageReadUse storageReadPhaseUse trieNodeMax readNodes
  rw [hs, hi, hx, ht, chargesUse_of hf hx, chargesUse_of hf hx]
  cases h.storage next <;> simp [chargesUse_of hf hx]

/-- The initial-state lookup cost exactly bounds the lookup after state_read. -/
theorem balanceReadGasAfterState_exact (cfg : WasmConfig) (h : NearState) (st : Near.TrieOverlay.State)
    (L : UInt32) (key : List UInt8) :
    ∀ h1, StorageReadPost h WNear.stateKey 0 st h1 →
      cost399None cfg 2 1 L h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) ≤
        cost399None cfg 2 1 L h (WNear.accountsPrefix ++ (bytes32 L ++ key)) := by
  intro h1 hread
  unfold cost399None
  rw [storageReadUse_after_read hread]

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The absent-account path with its exact post-state-read lookup gas. -/
theorem state_through_cleanup_exact_gas (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
    (p c L idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
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
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    stateCode e inst mi A n maxP mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (800 * cfg.regularOpCost + cost219 cfg h S +
        (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + cost399None cfg 2 1 L h (WNear.accountsPrefix ++ (bytes32 L ++ key)) +
          (17 * cfg.regularOpCost + cost96F cfg 5 0 0 +
            (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h 3 + (660 * cfg.regularOpCost + R))))))) ∗
      pre219 n g ta A gt s (s + 88) idx maxP len ((p.toNat, c.toNat) :: live) oldState h [.i32 (s + 88)] ∗
      n ↦[wms][ (s + 48).toNat ] oldContract ∗ n ↦[wms][ (s + 32).toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗
      n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ p.toNat + key.length ] rest ∗ n ↦[wms][ (s + 8).toNat ] ob ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n maxP hl live 8) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s x1 x2 (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 (s + 40)) [] ((f297.body.drop 68).take 82) Φ := by
  exact state_through_cleanup_of_budget cfg lim d inst e mi A n g ta mx hm hd Cg R
    (cost399None cfg 2 1 L h (WNear.accountsPrefix ++ (bytes32 L ++ key))) gt s x1 x2 p c L idx maxP len live
    key rest ob oldState oldContract dest out head hs hal hframe hkey hrest hc hL hp hob holdState holdContract hdest hout hhead
    h S st hv hr1 hr2 hroom hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg
    (balanceReadGasAfterState_exact cfg h st L key) ptr0 hret Φ

end Spec

end WNear.Binary.BalanceOf297AbsentCall
