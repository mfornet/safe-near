import Bridge.Functions.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOfPresent (code293 pre293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.AllocInv (heapInv_perm)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.StateReadModel (contractBytes accountsPrefix_length)
open WNear.Binary.StateReadLen (LenStep)
open WNear.Binary.FtTotalSupply (contractBytes_split u128_length u64_length storageReadPost_config)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open WNear.Binary.BalanceOf297AbsentCall (cost219F state_read_and_unwrapF)

/-- Precisely the second storage-read premises after the state read, including its gas bound. -/
def PresentBalanceReadAfterStateF (cfg : WasmConfig) (F : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (L : UInt32) (lo hi : UInt64) (key : List UInt8) (K : Nat) : Prop :=
  ∀ h1, StorageReadPost h WNear.stateKey 0 st h1 →
    ∃ st1 bud, h1.storageAccounting = some st1 ∧
      withinLimit h1.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 L ++ key)).length = true ∧
      build st1.entries = .ok st1.base ∧ zeroHash ∉ st1.base.witness.map Prod.fst ∧
      h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) =
        viewVal st1 (contractKey h1.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key))) ∧
      ProofBudget h1 st1 bud ∧
      readProofCost (contractKey h1.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key)))
        (h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key))) ≤ bud ∧
      h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) = some (u128Bytes lo hi) ∧
      cost399 cfg (F + 1) 1 L h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) (u128Bytes lo hi) ≤ K

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- From state read and an owned parsed account to the present-account result and epilogue. -/
theorem state_through_cleanup_presentF (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R K : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
    (p c L idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (lo hi : UInt64)
    (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hob : ob.length = 16) (holdState : oldState.length = 40) (holdContract : oldContract.length = 40)
    (hdest : dest.length = 16) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hr1 : roomFor len maxP 29)
    (hr2 : ∀ len1, len1 = len ∨ len1 = grownLen len 29 → roomFor len1 maxP 1)
    (hroom : ∀ len1, LenStep len 29 1 len1 → HeapRoomK 5 len1 maxP)
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey))
    (hproof : ProofBudget h st (readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true) (hnext : PresentBalanceReadAfterStateF cfg F h st L lo hi key K)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF) :
    stateCodeF e inst mi A n maxP mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (800 * cfg.regularOpCost + cost219F cfg F h S +
        (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + K +
          (17 * cfg.regularOpCost + cost96F cfg ((F + 1) + 4) lo hi +
            (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R))))))) ∗
      pre219F n g ta A gt s (s + 88) idx maxP len ((p.toNat, c.toNat) :: live) F oldState h [.i32 (s + 88)] ∗
      n ↦[wms][ (s + 48).toNat ] oldContract ∗ n ↦[wms][ (s + 32).toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗
      n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ p.toNat + key.length ] rest ∗ n ↦[wms][ (s + 8).toNat ] ob ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n maxP hl live ((((F + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s x1 x2 (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 (s + 40)) [] ((f297.body.drop 68).take 82) Φ := by
  iintro ⟨#HSC, #F219, #F155, #F951, #HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456,
    #Hdrop, #F68, #HIC, #Hi, Hc, HP, Hcontract, Hsrc, Hkey, Hrest, Hob, Hdest, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 68).take 82 =
      (f297.body.drop 68).take 11 ++ (f297.body.drop 79).take 71 := by rfl
  rw [hseg]
  have hframeEq : frame inst mi s x1 x2 (s + 40) = WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40) := rfl
  rw [hframeEq]
  iapply mwpi_seq
  iapply (state_read_and_unwrapF cfg lim d inst e mi A n g ta mx hm (by omega) Cg
    (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + K +
      (17 * cfg.regularOpCost + cost96F cfg ((F + 1) + 4) lo hi +
        (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R))))))
    gt s x1 x2 (s + 40) idx maxP len ((p.toNat, c.toNat) :: live) F hF oldState oldContract hs hal hframe
    holdState holdContract h S hv hr1 hr2 st hacc hlim hb hz hlink hproof hreg)
  iframe HSC F219 F155 F951 Hi Hc HP Hcontract
  inext
  iintro %rs Hstate
  icases Hstate with ⟨Hc, %hrs, Hg, HI, Hs, Hvt, HstateKey, %pv, %pp, %pad, %len1, %⟨hpad, hstep⟩,
    Hopt, Hcontract, Hinv, Hprefix, %h1, %hread, Hhost⟩
  subst hrs
  obtain ⟨st1, bud, ha1, hl1, hb1, hz1, hlink1, hp1, hbud1, hsome1, hcost1⟩ := hnext h1 hread
  have hcfg := storageReadPost_config hread
  have hret1 : withinLimit h1.config.maxReturnLen (resultLen lo hi).toNat = true := by rw [hcfg.1]; exact hret
  have hreg1 : withinLimit h1.config.maxRegisterLen 16 = true := by
    rw [hcfg.1]
    cases hreglim : h.config.maxRegisterLen with
    | none => simp [withinLimit]
    | some k => simp [withinLimit, hreglim] at hreg ⊢; omega
  have hvr : valueReturnUse h1 (resultLen lo hi).toNat = valueReturnUse h (resultLen lo hi).toNat := hcfg.2 (resultLen lo hi).toNat
  have hprefixLen : WNear.accountsPrefix.length = 1 := accountsPrefix_length
  have hpre : WNear.accountsPrefix.length = (1 : UInt32).toNat := by simp [hprefixLen]
  have hlive : ((pp.toNat, 1) :: (pv.toNat, 29) :: (p.toNat, c.toNat) :: live).erase (pv.toNat, 29) =
      (pp.toNat, 1) :: (p.toNat, c.toNat) :: live := by simp
  rw [hlive]
  ihave Hinv := heapInv_perm n maxP len1 _ _ (F + 1) (List.Perm.swap _ _ _) $$ Hinv
  have hs8 : (contractBytes S pp ++ pad).length = 40 := by
    rw [List.length_append, FtTotalSupply.contractBytes_length, hpad]
  ihave Hopt := U128From.memBytes_split n (s + 88).toNat 12 (contractBytes S pp ++ pad) (by omega) $$ Hopt
  icases Hopt with ⟨Hold, Htail⟩
  ihave Htail := U128From.memBytes_split n ((s + 88).toNat + 12) 4 ((contractBytes S pp ++ pad).drop 12)
    (by simp [FtTotalSupply.contractBytes_length, hpad]) $$ Htail
  icases Htail with ⟨Htail, Hdiscard⟩
  ihave Htail := memBytes_addr (show (s + 88).toNat + 12 = (s + 100).toNat by
    simp [UInt32.toNat_add]; have := s.toNat_lt; omega) $$ Htail
  have hold12 : ((contractBytes S pp ++ pad).take 12).length = 12 := by simp [FtTotalSupply.contractBytes_length, hpad]
  have htail4 : (((contractBytes S pp ++ pad).drop 12).take 4).length = 4 := by simp [FtTotalSupply.contractBytes_length, hpad]
  ihave Hcontract : n ↦[wms][ (s + 48).toNat ]
      (WNear.Borsh.u128 S.totalSupply ++ (WNear.Borsh.u64 S.accountStorageUsage ++
        (bytes32 pp ++ (bytes32 1 ++ (bytes32 1 ++ pad))))) $$ [Hcontract]
  · rw [← contractBytes_split]
    iexact Hcontract
  icases BorshFT.splitB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 16)
    (WNear.Borsh.u128 S.totalSupply) _ (by simp [u128_length]) $$ Hcontract with ⟨Hdiscard2, Hcontract⟩
  icases BorshFT.splitB (n := n) (a := (s + 48).toNat + 16) (b := (s + 48).toNat + 24)
    (WNear.Borsh.u64 S.accountStorageUsage) _ (by simp [u64_length]) $$ Hcontract with ⟨Hdiscard3, Hcontract⟩
  rw [← List.append_assoc (bytes32 1) (bytes32 1) pad,
    ← List.append_assoc (bytes32 pp) (bytes32 1 ++ bytes32 1) pad]
  icases BorshFT.splitB (n := n) (a := (s + 48).toNat + 24) (b := (s + 48).toNat + 36)
    (bytes32 pp ++ (bytes32 1 ++ bytes32 1)) pad (by simp [bytes32_length]) $$ Hcontract with ⟨Hm, Hdiscard5⟩
  ihave Hm := memBytes_addr (show (s + 48).toNat + 24 = ((s + 48) + 24).toNat by
    simp [UInt32.toNat_add]; have := s.toNat_lt; omega) $$ Hm
  ihave Hm : prefixAt n ((s + 48) + 24) pp 1 1 $$ [Hm]
  · iunfold prefixAt
    iexact Hm
  icases stk_split n (s.toNat - 592) 176 416 $$ Hs with ⟨Hdiscard4, Hs⟩
  ihave Hs := stk_addr (show s.toNat - 592 + 176 = s.toNat - 416 by omega) $$ Hs
  icases stk_split n (s.toNat - 416) 32 384 $$ Hs with ⟨Hextra, Hs⟩
  ihave Hs := stk_addr (show s.toNat - 416 + 32 = s.toNat - 384 by omega) $$ Hs
  ihave HP : pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp 1 1 (s + 32) p c L
      idx maxP len1 ((pp.toNat, 1) :: live) (F + 1) WNear.accountsPrefix key rest ob h1
      [.i32 (s + 8), .i32 (s + 48), .i32 (s + 32)] $$ [Hg Hs HI Hvt Hinv Hm Hprefix Hsrc Hkey Hrest Hob Hhost]
  · iunfold pre293
    iframe Hg Hs HI Hvt Hinv Hm Hprefix Hsrc Hkey Hrest Hob Hhost
    ipureintro; rfl
  ihave Hpadding : n ↦[wms][ pp.toNat + WNear.accountsPrefix.length ] ([] : List UInt8) $$ []
  · iapply VecFromElem.memBytes_nil
  simp only [Post.mseq_normal]
  rw [← hframeEq]
  iapply (parsed_account_through_cleanup_present cfg lim d inst mi e A n g ta mx hm hd Cg R gt s x1 x2
    pp 1 1 p c L idx maxP len1 live (F + 1) (by unfold okG; omega) lo hi WNear.accountsPrefix key rest ob dest
    (((contractBytes S pp ++ pad).drop 12).take 4) out head [] ((contractBytes S pp ++ pad).take 12)
    (by omega) hal hframe hob hdest htail4 hout hhead hold12 (by simp [hprefixLen]) (by decide)
    hpre hkey hrest hc hL (by decide) (by decide) (by have := pp.toNat_lt; simp; omega) hp
    (hroom len1 hstep) h1 st1 ha1 hl1 hb1 hz1 hlink1 hp1 hbud1 hreg1 hsome1 ptr0 hret1 Φ)
  simp only [UInt32.reduceToNat]
  iframe HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi HP Hold Hextra Htail Hdest HD Hout Hhead Hpadding
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    rw [hvr]
    omega
  inext
  iintro ⟨Hc, Hg, Hinv, %h2, %hread2, Hhost⟩
  iapply HΦ $$ [Hc Hg Hinv Hhost]
  iframe Hc Hg Hinv Hhost
  iexists h1
  isplitr; · ipureintro; exact hread
  iexists st1
  ipureintro; exact hread2

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic
open WNear.Binary
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
/-- The existing storage-read transition discharges the second lookup's trie and proof budget. -/
theorem presentBalanceReadAfterState_exact_from_budget (cfg : WasmConfig) (F : Nat) (h : NearState) (st : Near.TrieOverlay.State)
    (L : UInt32) (lo hi : UInt64) (key : List UInt8) (bud : Nat) (hcanon : Canon st) (hlink : StorageLink h st)
    (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key))) ≤ bud)
    (hlim : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 L ++ key)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) = some (u128Bytes lo hi))
    : PresentBalanceReadAfterStateF cfg F h st L lo hi key
      (cost399 cfg (F + 1) 1 L h (WNear.accountsPrefix ++ (bytes32 L ++ key)) (u128Bytes lo hi)) := by
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
    hacc1, ?_, hcanon1.1, hcanon1.2, hlink1 _, hp1, ?_, ?_, ?_⟩
  · simpa [hcfg] using hlim
  · rw [hstorage, hid]
    omega
  · simpa [hstorage] using hsome

  · have hf : h1.fees = h.fees :=
      (erase_field he1 NearState.fees (fun _ => rfl)).trans
        (storageReadRegs_field NearState.fees (fun _ _ _ => rfl) _ _ _)
    have hx : h1.extCosts = h.extCosts :=
      (erase_field he1 NearState.extCosts (fun _ => rfl)).trans
        (storageReadRegs_field NearState.extCosts (fun _ _ _ => rfl) _ _ _)
    have hcost := StorageReadWrapF.cost523F_eq cfg (F + 1)
      (h := h) (val := u128Bytes lo hi) (h' := h1.setRegister 0 (u128Bytes lo hi))
      (by simp [NearState.setRegister])
      (fun cs => StorageReadWrap.chargesUse_congr' (by exact hf) (by exact hx) cs)
    unfold cost399 StorageReadWrapF.costSF
    rw [WNear.Binary.BalanceOf297AbsentCall.storageReadUse_after_read hread, hcost]

end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOfPresent (code293 pre293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.AllocInv (heapInv_perm)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.StateReadModel (contractBytes accountsPrefix_length)
open WNear.Binary.StateReadLen (LenStep)
open WNear.Binary.FtTotalSupply (contractBytes_split u128_length u64_length storageReadPost_config)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

open WNear.Binary.BalanceOf297AbsentCall (cost219F state_read_and_unwrapF)

open WNear.Binary.LookupMapOps (LenIn roomFor_ofK lenIn_zero lenIn_step)
open WNear.Binary.FtTotalSupply (lenStep_bounds)
/-- Seven initial growth slots cover state_read's two and the balance suffix's five. -/
theorem present_room_after_state (len maxP : Nat) (h : HeapRoomK 7 len maxP) :
    roomFor len maxP 29 ∧
    (∀ len1, len1 = len ∨ len1 = grownLen len 29 → roomFor len1 maxP 1) ∧
    (∀ len1, LenStep len 29 1 len1 → HeapRoomK 5 len1 maxP) := by
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
theorem state_through_cleanup_present_seven_growsF (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
    (p c L idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (lo hi : UInt64)
    (key rest ob oldState oldContract dest out head : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hob : ob.length = 16) (holdState : oldState.length = 40) (holdContract : oldContract.length = 40)
    (hdest : dest.length = 16) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hroom : HeapRoomK 7 len maxP)
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 L ++ key)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF) :
    stateCodeF e inst mi A n maxP mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (800 * cfg.regularOpCost + cost219F cfg F h S +
        (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + cost399 cfg (F + 1) 1 L h (WNear.accountsPrefix ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
          (17 * cfg.regularOpCost + cost96F cfg ((F + 1) + 4) lo hi +
            (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R))))))) ∗
      pre219F n g ta A gt s (s + 88) idx maxP len ((p.toNat, c.toNat) :: live) F oldState h [.i32 (s + 88)] ∗
      n ↦[wms][ (s + 48).toNat ] oldContract ∗ n ↦[wms][ (s + 32).toNat ] (bytes32 p ++ (bytes32 c ++ bytes32 L)) ∗
      n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ p.toNat + key.length ] rest ∗ n ↦[wms][ (s + 8).toNat ] ob ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n maxP hl live ((((F + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s x1 x2 (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 (s + 40)) [] ((f297.body.drop 68).take 82) Φ := by
  obtain ⟨hr1, hr2, hroom'⟩ := present_room_after_state len maxP hroom
  have hnext := presentBalanceReadAfterState_exact_from_budget cfg F h st L lo hi key bud hcanon hlink hproof hbudget hlimAccount hsome
  exact state_through_cleanup_presentF cfg lim d inst e mi A n g ta mx hm hd Cg R
    (cost399 cfg (F + 1) 1 L h (WNear.accountsPrefix ++ (bytes32 L ++ key)) (u128Bytes lo hi))
    gt s x1 x2 p c L idx maxP len live F hF lo hi key rest ob oldState oldContract dest out head
    hs hal hframe hkey hrest hc hL hp hob holdState holdContract hdest hout hhead h S st hv hr1 hr2 hroom'
    hacc hlim hcanon.1 hcanon.2 (hlink _) (hproof.mono (by omega)) hreg hnext ptr0 hret Φ

end Spec
end WNear.Binary.BalanceOf297PresentCall

/-! Compose the decoded parser success handoff with state read and absent balance cleanup. -/
