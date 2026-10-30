import Bridge.Functions.BalanceOf297ReadGas

/-! Derive all state-read and subsequent lookup room from one initial growth budget. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateRead (stateCode pre219)
open WNear.Binary.StateReadLen (LenStep)
open WNear.Binary.VecFromElem (roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_zero lenIn_step)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.FtTotalSupply (cost219 lenStep_bounds)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

/-- Six initial growth slots cover state_read's two and the balance suffix's four. -/
theorem room_after_state (len maxP : Nat) (h : HeapRoomK 6 len maxP) :
    roomFor len maxP 29 ∧
    (∀ len1, len1 = len ∨ len1 = grownLen len 29 → roomFor len1 maxP 1) ∧
    (∀ len1, LenStep len 29 1 len1 → HeapRoomK 4 len1 maxP) := by
  have hzero : LenIn len 0 len := lenIn_zero len h.1
  refine ⟨roomFor_ofK 29 (by decide) h hzero (by omega), ?_, ?_⟩
  · intro len1 hstep
    exact roomFor_ofK 1 (by decide) h (lenIn_step 29 (by decide) hzero hstep) (by omega)
  · intro len1 hstep
    obtain ⟨hlow, hhigh, halign⟩ := lenStep_bounds len len1 h.1 hstep
    obtain ⟨_, hpos, hmax, h32⟩ := h
    unfold HeapRoomK
    exact ⟨halign, by omega, by omega, by omega⟩

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The composed absent-account path under a single initial six-growth bound. -/
theorem state_through_cleanup_six_grows (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
    (p c L idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat))
    (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hob : ob.length = 16) (holdState : oldState.length = 40) (holdContract : oldContract.length = 40)
    (hdest : dest.length = 16) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hroom : HeapRoomK 6 len maxP)
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
  obtain ⟨hr1, hr2, hroom'⟩ := room_after_state len maxP hroom
  exact state_through_cleanup_exact_gas cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 p c L idx maxP len live
    key rest ob oldState oldContract dest out head hs hal hframe hkey hrest hc hL hp hob holdState holdContract hdest hout hhead
    h S st hv hr1 hr2 hroom' hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ

end Spec
end WNear.Binary.BalanceOf297AbsentCall
