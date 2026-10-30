import Bridge.Functions.BalanceOf297StateRead
import Bridge.Functions.AllocLivePerm

/-! Compose state loading with the parsed absent-account suffix. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293 pre293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.AllocInv (heapInv_perm)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.StateRead (stateCode pre219)
open WNear.Binary.StateReadModel (contractBytes accountsPrefix_length)
open WNear.Binary.StateReadLen (LenStep)
open WNear.Binary.FtTotalSupply (cost219 contractBytes_split u128_length u64_length storageReadPost_config)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

/-- Precisely the second storage-read premises after the state read, including its gas bound. -/
def BalanceReadAfterState (cfg : WasmConfig) (h : NearState) (st : Near.TrieOverlay.State)
    (L : UInt32) (key : List UInt8) (K : Nat) : Prop :=
  ∀ h1, StorageReadPost h WNear.stateKey 0 st h1 →
    ∃ st1 bud, h1.storageAccounting = some st1 ∧
      withinLimit h1.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 L ++ key)).length = true ∧
      build st1.entries = .ok st1.base ∧ zeroHash ∉ st1.base.witness.map Prod.fst ∧
      h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) =
        viewVal st1 (contractKey h1.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key))) ∧
      ProofBudget h1 st1 bud ∧
      readProofCost (contractKey h1.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key)))
        (h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key))) ≤ bud ∧
      h1.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) = none ∧
      cost399None cfg 2 1 L h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) ≤ K

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- From state read and an owned parsed account to the absent-account result and epilogue. -/
theorem state_through_cleanup_absent (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R K : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
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
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey))
    (hproof : ProofBudget h st (readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true) (hnext : BalanceReadAfterState cfg h st L key K)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    stateCode e inst mi A n maxP mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (800 * cfg.regularOpCost + cost219 cfg h S +
        (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + K +
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
  iintro ⟨#HSC, #F219, #F155, #F951, #HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456,
    #Hdrop, #F68, #HIC, #Hi, Hc, HP, Hcontract, Hsrc, Hkey, Hrest, Hob, Hdest, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 68).take 82 =
      (f297.body.drop 68).take 11 ++ (f297.body.drop 79).take 71 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (state_read_and_unwrap cfg lim d inst e mi A n g ta mx hm (by omega) Cg
    (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + K +
      (17 * cfg.regularOpCost + cost96F cfg 5 0 0 +
        (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h 3 + (660 * cfg.regularOpCost + R))))))
    gt s x1 x2 (s + 40) idx maxP len ((p.toNat, c.toNat) :: live) oldState oldContract hs hal hframe
    holdState holdContract h S hv hr1 hr2 st hacc hlim hb hz hlink hproof hreg)
  iframe HSC F219 F155 F951 Hi Hc HP Hcontract
  inext
  iintro %rs Hstate
  icases Hstate with ⟨Hc, %hrs, Hg, HI, Hs, Hvt, HstateKey, %pv, %pp, %pad, %len1, %⟨hpad, hstep⟩,
    Hopt, Hcontract, Hinv, Hprefix, %h1, %hread, Hhost⟩
  subst hrs
  obtain ⟨st1, bud, ha1, hl1, hb1, hz1, hlink1, hp1, hbud1, hnone1, hcost1⟩ := hnext h1 hread
  have hcfg := storageReadPost_config hread
  have hret1 : withinLimit h1.config.maxReturnLen 3 = true := by rw [hcfg.1]; exact hret
  have hvr : valueReturnUse h1 3 = valueReturnUse h 3 := hcfg.2 3
  have hprefixLen : WNear.accountsPrefix.length = 1 := accountsPrefix_length
  have hpre : WNear.accountsPrefix.length = (1 : UInt32).toNat := by simp [hprefixLen]
  have hlive : ((pp.toNat, 1) :: (pv.toNat, 29) :: (p.toNat, c.toNat) :: live).erase (pv.toNat, 29) =
      (pp.toNat, 1) :: (p.toNat, c.toNat) :: live := by simp
  rw [hlive]
  ihave Hinv := heapInv_perm n maxP len1 _ _ 2 (List.Perm.swap _ _ _) $$ Hinv
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
      idx maxP len1 ((pp.toNat, 1) :: live) 2 WNear.accountsPrefix key rest ob h1
      [.i32 (s + 8), .i32 (s + 48), .i32 (s + 32)] $$ [Hg Hs HI Hvt Hinv Hm Hprefix Hsrc Hkey Hrest Hob Hhost]
  · iunfold pre293
    iframe Hg Hs HI Hvt Hinv Hm Hprefix Hsrc Hkey Hrest Hob Hhost
    ipureintro; rfl
  ihave Hpadding : n ↦[wms][ pp.toNat + WNear.accountsPrefix.length ] ([] : List UInt8) $$ []
  · iapply VecFromElem.memBytes_nil
  simp only [Post.mseq_normal]
  iapply (parsed_account_through_cleanup_absent cfg lim d inst mi e A n g ta mx hm hd Cg R gt s x1 x2
    pp 1 1 p c L idx maxP len1 live 2 (by decide) WNear.accountsPrefix key rest ob dest
    (((contractBytes S pp ++ pad).drop 12).take 4) out head [] ((contractBytes S pp ++ pad).take 12)
    (by omega) hal hframe hob hdest htail4 hout hhead hold12 (by simp [hprefixLen]) (by decide)
    hpre hkey hrest hc hL (by decide) (by decide) (by have := pp.toNat_lt; simp; omega) hp
    (hroom len1 hstep) h1 st1 ha1 hl1 hb1 hz1 hlink1 hp1 hbud1 hnone1 ptr0 hret1 Φ)
  simp only [UInt32.reduceToNat]
  iframe HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi HP Hold Hextra Htail Hdest HD Hout Hhead Hpadding
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    rw [hvr]
    simp only [Nat.reduceAdd]
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
end WNear.Binary.BalanceOf297AbsentCall
