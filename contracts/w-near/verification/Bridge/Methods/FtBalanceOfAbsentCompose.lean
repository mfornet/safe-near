import Bridge.Functions.BalanceOf297InitialRoomCompose
import Bridge.Methods.FtBalanceOfModel
import Bridge.Functions.BalanceOf297Prologue
import Bridge.Functions.BalanceOf297InputSetup
import Bridge.Functions.EnvInput
import Bridge.Functions.AllocZeroed
import Bridge.Functions.BalanceOf297CopiedParser
import Bridge.Functions.BalanceOf297ParserPublicCompose

/-! Check the absent-account decoded execution together with its boundary model result. -/
namespace WNear.Binary.FtBalanceOfMethod

open Wasm Wasm.Near WasmLogic NearLogic NearInterface
open WNear.Binary.NearDepositMethod
open WNear.Binary.FtTotalSupplyMethod

/-- Under the storage representation and no storage deficit, an absent account
    has the zero balance returned by the checked binary path. -/
theorem absent_step_zero (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (s : WNear.State)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode s) (hs : s.WF) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (a : WNear.AccountId)
    (hnone : h.storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none)
    (hdef : ¬ 0 < deficit ctx s) :
    (WNear.wnear cfg).step ctx (some s) (.ftBalanceOf a) =
      .ok { state := s, ret := .u128 0, logs := [], promises := [] } := by
  obtain ⟨reg, hreg, hstep⟩ := account_lookup_and_step cfg ctx raw s hwf hraw hs h he a.toNear
  simp only [WNear.AccountId.ofNear_toNear] at hstep
  have hn : reg = none := by
    have hlen : a.val.toUTF8.toList.length = a.val.utf8ByteSize := by
      rw [Wasm.ByteEncoding.byteArray_toList_length]
      simp [String.toUTF8_eq_toByteArray]
    change h.storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.toUTF8.toList.length) ++ a.val.toUTF8.toList)) = _ at hreg
    rw [hlen, hnone] at hreg
    cases reg with
    | none => rfl
    | some p =>
      simp only [Option.map_some] at hreg
      cases hreg
  simp [hn, hdef] at hstep
  exact hstep

end WNear.Binary.FtBalanceOfMethod


namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.ToVec
open WNear.Binary.FtTotalSupply (codeA vtab)
open WNear.Binary.SetupPanicHook (hookCells)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
open WNear.Binary.Interface (dataWord)
open WNear.Binary.EnvInput (inCode pre527 post527 ifaceI cost527 f527_spec)
open WNear.Binary.ReadRegister (RegOk optVecAt)
open WNear.Binary.VecFromElem (stk_split stk_join stk_addr grownLen)
open WNear.Binary.VecFromElem (stk_split stk_join stk_addr)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStr (borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeStruct78Esc (costArray)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem copied_array_absent_body_model_agreement (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat))
    (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (j k : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 < 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length))]? = some 0x5D)
    (hk : k = bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, jsonRest))
    (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hparserRoom : ∀ len', len' = len ∨ len' = grownLen len (UInt32.ofNat bs.length) →
      roomRun 2048 len' 0 [] (bs.drop (j + 1)))
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true)
    (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hroom : HeapRoomK ((AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat + copiedParserPages bs (j + 1) a + 6) len 2048)
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hnone : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none)
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true)
    (modelCfg : WNear.Config) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (hwf : ctx.WF raw) (hraw : raw = WNear.encode S) (hS : S.WF)
    (hrep : eraseP h = eraseP (hostOf ctx raw))
    (hdef : ¬ 0 < WNear.Binary.FtTotalSupplyMethod.deficit ctx S) (Φ : Post NearState GF) :
    ((WNear.wnear modelCfg).step ctx (some S) (.ftBalanceOf a) =
      .ok { state := S, ret := .u128 0, logs := [], promises := [] }) ∧
    (codeA inst mi A ∗ inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg 1 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost cfg (copiedParserFree bs (j + 1) 1) h S a R)))))) ∗
      g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ stk n (s.toNat - 592) 592 ∗
      hookCells n 0 hookOld 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
      n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ ta ↦[wt][ 44 ] Ref.func (A 246) ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
      n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] oldVec ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        (∃ ip : UInt32, n ↦[i32][ (s + 24).toNat ] ip) ∗
        n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((copiedParserFree bs (j + 1) 1 + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d ⟨#[.i32 0, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩ [] f297.body Φ) := by
  constructor
  · exact WNear.Binary.FtBalanceOfMethod.absent_step_zero modelCfg ctx raw S hwf hraw hS h hrep a hnone hdef
  · exact copied_array_absent_body_initial_room cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
      idx len a live bs oldOpt optTail oldVec jsonRest derefOut j k ob stateTail contractTail destTail out head
      oldA oldB oldC oldD hookOld k3 hs hal hframe hopt hoptTail holdVec hderef hlen ho hj hq he hk hend hmodel
      hcopied hparserRoom hob hstateTail hcontractTail hdestTail hA hB hout hhead h0 h hinput hafter
      hinputLimit S st hv hroom hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ

end Spec
end WNear.Binary.BalanceOf297AbsentCall
