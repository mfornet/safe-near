import Bridge.Functions.BalanceOf297StateRead
import Bridge.Functions.StateReadLenF
import Bridge.Functions.FtTotalSupply

/-! Read the deployed contract state and unwrap its successful result. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.StateReadLenF (stateCodeF pre219F postModelLF f219_spec_model_lenF)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.StorageReadWrapF (costSF)
open WNear.Binary.BorshContractF (cost161)
open WNear.Binary.StateReadModel (contractBytes)
open WNear.Binary.StateReadLen (LenStep)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.FtTotalSupply (heapInv_live8 contractBytes_length contractBytes_split u128_length u64_length)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay


def cost219F (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State) : Nat :=
  105 * cfg.regularOpCost +
    (40 * cfg.regularOpCost + (249 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5) +
      costSF cfg F h (WNear.header S)) +
    cost161 cfg F 1 + 726 * cfg.regularOpCost + 334 * cfg.regularOpCost

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- Read a present model state and copy its contract value into the balance frame. -/
theorem state_read_and_unwrapF (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 18 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (ob old : List UInt8) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0) (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (hob : ob.length = 40) (hold : old.length = 40) (h : NearState) (S : WNear.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hr1 : roomFor len maxP 29)
    (hr2 : ∀ len', len' = len ∨ len' = grownLen len 29 → roomFor len' maxP 1)
    (st : Near.TrieOverlay.State) (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage WNear.stateKey = viewVal st (contractKey h.context.currentAccountId WNear.stateKey))
    (hproof : ProofBudget h st (readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey)))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true) (Φ : Post NearState GF) :
    stateCodeF e inst mi A n maxP mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      inst ↪[inst] mi ∗ credits Cg (800 * cfg.regularOpCost + cost219F cfg F h S + R) ∗
      pre219F n g ta A gt s (s + 88) idx maxP len live F ob h [.i32 (s + 88)] ∗
      n ↦[wms][ (s + 48).toNat ] old ∗
      ▷ (∀ rs, (credits Cg R ∗ ⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗
        stk n (s.toNat - 592) 592 ∗ vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗
        ∃ pv p : UInt32, ∃ pad : List UInt8, ∃ len' : Nat, ⌜pad.length = 4 ∧ LenStep len 29 1 len'⌝ ∗
          n ↦[wms][ (s + 88).toNat ] (contractBytes S p ++ pad) ∗
          n ↦[wms][ (s + 48).toNat ] (contractBytes S p ++ pad) ∗
          heapInv n maxP len' (((p.toNat, 1) :: (pv.toNat, 29) :: live).erase (pv.toNat, 29)) (F + 1) ∗
          n ↦[wms][ p.toNat ] WNear.accountsPrefix ∗
          ∃ h', ⌜StorageReadPost h WNear.stateKey 0 st h'⌝ ∗ mhostPt h') -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 68).take 11) Φ := by
  iintro ⟨#HSC, #F219, #F155, #F951, #Hi, Hc, HP, Hold, HΦ⟩
  unfold cost219F
  have hn := hm.mem
  have ha219 := hm.funcs 219 (by decide)
  have ha155 := hm.funcs 155 (by decide)
  have ha951 := hm.funcs 951 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have t14 : types[14]!.params.length = 2 := rfl
  have t15 : types[15]!.params.length = 3 := rfl
  have hlt := s.toNat_lt
  rw [stateCode297_eq]
  simp only [stateCode297, frame]
  mstep; mstep; mstep
  mcall (f219_spec_model_lenF cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    s (s + 88) hs hal (by simp [UInt32.toNat_add]; omega) idx maxP len live F hF ob hob h S hv hr1 hr2
    st hacc hlim hb hz hlink hproof hreg) using [HP]
    with (mstep_norm_full; omega)
  · iexact HP
  iunfold postModelLF at HQ
  icases HQ with ⟨%hrs, Hg, HI, Hs, Hvt, Hkey, ⟨%pv, %p, %pad, %len', %⟨hpad, hstep⟩, Hopt, Hinv, Hp⟩,
    ⟨%h', %hread, Hhost⟩⟩
  subst hrs
  ihave Hinv := heapInv_live8 n maxP len' _ (F + 1) $$ Hinv
  icases Hinv with ⟨%h8, Hinv⟩
  have hp8 : 8 ≤ p.toNat := h8 _ 1 (by simp)
  have hsb : (contractBytes S p ++ pad).length = 40 := by rw [List.length_append, contractBytes_length, hpad]
  have hniche : ((contractBytes S p ++ pad).drop 24).take 4 = bytes32 p := by
    rw [contractBytes_split]; simp [List.drop_append, List.take_append, u128_length, u64_length]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (UnwrapOrDefault.f155_spec cfg lim (d + 1) types[14]! rfl inst mi n (A 951) hn ha951
    types[15]! rfl rfl (by omega) Cg (s + 48) (s + 88)
    (by simp [UInt32.toNat_add]; omega) (by simp [UInt32.toNat_add]; omega) old
    (contractBytes S p ++ pad) hold hsb (by rw [hniche, decodeLE_bytes32]; omega)) using [Hold Hopt]
  · iunfold UnwrapOrDefault.pre
    iframe Hold Hopt
    ipureintro; rfl
  iunfold UnwrapOrDefault.post at HQ
  icases HQ with ⟨%hrs, Hcopy, Hopt⟩
  mcredits R
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc Hg HI Hs Hvt Hkey Hopt Hcopy Hinv Hp Hhost]
  iframe Hc Hg HI Hs Hvt Hkey Hopt Hcopy Hinv Hp Hhost
  isplitr; · ipureintro; exact hrs
  isplitr; · ipureintro; exact ⟨hpad, hstep⟩
  ipureintro; simpa [StateRead.stateKey_eq] using hread

end Spec
end WNear.Binary.BalanceOf297AbsentCall
