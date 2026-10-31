import Bridge.Methods.FtBalanceOfProviderInitial
import Bridge.Functions.SerdeObjectPresentProvider
import Bridge.Functions.BalanceOf297ParserFamily

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- A parser provider valid at every actual call site reachable after input allocation.
Its input grammar and gas proof remain the provider's responsibility. -/
def PresentParserFamily (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (gt : GlobalType) (bs : List UInt8) (a : WNear.AccountId)
    (F parseGas outF : Nat) (Cd : IProp GF) : Prop :=
  ∀ (Cg d : Nat) (sp out ptr idx : UInt32) (ob : List UInt8) (len : Nat) (live : List (Nat × Nat)),
    d + 45 < lim.maxCallDepth → ob.length = 16 → out.toNat + 16 ≤ 2 ^ 32 →
    bs.length < 2 ^ 24 → ptr.toNat + bs.length < 2 ^ 32 → 448 ≤ sp.toNat → sp.toNat % 8 = 0 →
    (len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length)) →
    PresentParserCallContract cfg lim d inst mi A n g ta Cg gt sp out ptr idx ob bs a len live F parseGas outF
      Cd (SerdeObjectNoEsc.parserStatics n)

end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (deref_and_parser_setup)
open WNear.Binary.BalanceOfPresent (code293)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.ToVec
open WNear.Binary.VecFromElem (stk_split stk_join stk_addr)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStr (borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeStruct78Esc (costArray)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_deref_parser_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat) (lo hi : UInt64)
    (bs tail parserOut derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (hparserOut : parserOut.length = 16) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (hL : len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF)
    (hFamily : PresentParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd) :
    Cd ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        parseGas +
        presentParserSuccessCost cfg (outF) h S a lo hi R)) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗ n ↦[wms][ (s + 88).toNat ] parserOut ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] (bytes32 ip ++ (bytes32 ic ++ bytes32 (UInt32.ofNat bs.length))) ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        n ↦[i32][ (s + 24).toNat ] ip ∗ n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((outF + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 21).take 129) Φ := by
  iintro ⟨#HCd, #HC66, #H169, #H646, #F644, #F66, #F65, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, HparserOut, Hbs, Htail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 21).take 129 =
      (f297.body.drop 21).take 14 ++ (f297.body.drop 35).take 115 := by rfl
  rw [hseg]
  have hframeEq : ∀ a b c, frame inst mi s a b c = WNear.Binary.BalanceOf297AbsentCall.frame inst mi s a b c := fun _ _ _ => rfl
  simp only [hframeEq]
  iapply mwpi_seq
  iapply (deref_and_parser_setup cfg lim d inst mi A n hm.mem (hm.funcs 779 (by decide)) (by omega) Cg
    (1000 * cfg.regularOpCost +
      parseGas +
      presentParserSuccessCost cfg (outF) h S a lo hi R)
    s x1 x2 x3 ip ic (UInt32.ofNat bs.length) derefOut hderef hframe)
  iframe Hi F779 Hc Hderef Hvec
  inext
  iintro ⟨Hc, P, L, Hvec⟩
  icases BorshFT.splitB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 4)
    (bytes32 ip) (bytes32 ic ++ bytes32 (UInt32.ofNat bs.length)) (by simp) $$ Hvec with ⟨I0, Irest⟩
  icases BorshFT.split64' (n := n) (a := (s + 48).toNat + 4) (b := (s + 48).toNat + 8)
    ic (UInt32.ofNat bs.length) (by omega) $$ Irest with ⟨I4, I8⟩
  simp only [Post.mseq_normal]
  simp only [← hframeEq]
  have hParser := hFamily Cg (d + 1) s (s + 88) ip idx parserOut len
    ((ip.toNat, ic.toNat) :: live) (by omega) hparserOut
    (by simp [UInt32.toNat_add]; omega) hlen hptr (by omega) hal hL
  iapply (parser_provider_through_cleanup_present cfg lim d inst e mi A n g ta mx hm (by omega) Cg R gt s x1 x2 x3
    ip ic idx len a live F lo hi bs tail parserOut parseGas outF Cd (SerdeObjectNoEsc.parserStatics n)
    ob stateTail contractTail destTail out head oldA oldB oldC oldD
    hs hal hframe hic hinput hparserOut hob hstateTail hcontractTail hdestTail hA hB hout hhead
    h S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hsome hreg ptr0 hret Φ hParser)
  iframe HCd F65 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi
    Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv HparserOut Hbs Htail Hesc Hutf Hhex HFr HstateTail A0 A8 HdestTail B0 B8
    I0 I4 I8 HcontractTail Hob HD Hout Hhead
  inext
  iintro %p %c Hpost
  icases Hpost with ⟨Hc, Hesc, Hutf, Hhex, HFr, Hg, Hinv, Hhost⟩
  ispecialize HΦ $$ %p %c
  iapply HΦ $$ [Hc P L Hesc Hutf Hhex HFr Hg Hinv Hhost]
  simp only [List.cons_append, List.nil_append]
  iframe Hc P L Hesc Hutf Hhex HFr Hg Hinv Hhost

end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (input_expect)
open WNear.Binary.BalanceOfPresent (code293)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.ToVec
open WNear.Binary.VecFromElem (stk_split stk_join stk_addr)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStr (borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeStruct78Esc (costArray)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_expect_deref_parser_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat) (lo hi : UInt64)
    (bs tail optTail oldVec derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hip : ip ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (hL : len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF)
    (hFamily : PresentParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd) :
    Cd ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        parseGas +
        presentParserSuccessCost cfg (outF) h S a lo hi R))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗
      n ↦[i32][ (s + 88).toNat ] ip ∗ n ↦[i32][ (s + 88).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 88).toNat + 8 ] UInt32.ofNat bs.length ∗ n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
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
        n ↦[i32][ (s + 24).toNat ] ip ∗ n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((outF + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 13).take 137) Φ := by
  iintro ⟨#HCd, #HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, O0, O4, O8, HoptTail, Hbs, Htail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 13).take 137 =
      (f297.body.drop 13).take 8 ++ (f297.body.drop 21).take 129 := by rfl
  rw [hseg]
  have hframeEq : ∀ a b c, frame inst mi s a b c = WNear.Binary.BalanceOf297AbsentCall.frame inst mi s a b c := fun _ _ _ => rfl
  simp only [hframeEq]
  iapply mwpi_seq
  iapply (input_expect cfg lim d inst mi A n hm.mem (hm.funcs 157 (by decide)) (by omega) Cg
    (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
      parseGas +
      presentParserSuccessCost cfg (outF) h S a lo hi R))
    s x1 x2 x3 ip ic (UInt32.ofNat bs.length) oldVec holdVec hip hframe)
  iframe Hi F157 Hc Hvec O0 O4 O8
  inext
  iintro ⟨Hc, O0, O4, O8, V0, V4, V8⟩
  ihave OptTail := AllocNewCell.memBytes_addr (show (s + 100).toNat = (s + 88).toNat + 12 by
    simp [UInt32.toNat_add]; have := s.toNat_lt; omega) $$ HoptTail
  ihave Opt := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 4)
    (bytes32 ip) (bytes32 ic) (by simp) $$ [O0 O4]
  · iframe O0 O4
  ihave Opt := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 8)
    (bytes32 ip ++ bytes32 ic) (bytes32 (UInt32.ofNat bs.length)) (by simp [bytes32_length]) $$ [Opt O8]
  · iframe Opt O8
  ihave Opt := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 12)
    ((bytes32 ip ++ bytes32 ic) ++ bytes32 (UInt32.ofNat bs.length)) optTail (by simp [bytes32_length]) $$ [Opt OptTail]
  · iframe Opt OptTail
  ihave Vec := BorshFT.joinB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 4)
    (bytes32 ip) (bytes32 ic) (by simp) $$ [V0 V4]
  · iframe V0 V4
  ihave Vec := BorshFT.joinB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 8)
    (bytes32 ip ++ bytes32 ic) (bytes32 (UInt32.ofNat bs.length)) (by simp [bytes32_length]) $$ [Vec V8]
  · iframe Vec V8
  simp only [Post.mseq_normal]
  simp only [← hframeEq]
  iapply (provider_deref_parser_through_cleanup_present cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    ip ic idx len a live F lo hi bs tail (((bytes32 ip ++ bytes32 ic) ++ bytes32 (UInt32.ofNat bs.length)) ++ optTail)
    derefOut parseGas outF Cd ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic
    hinput (by simp [bytes32_length, hoptTail]) hderef hlen hptr hL hob hstateTail hcontractTail hdestTail hA hB hout hhead h S st hv hacc hlim hcanon hlink bud
    hproof hbudget hlimAccount hsome hreg ptr0 hret Φ hFamily)
  simp only [List.append_assoc] at *
  iframe HCd HC66 H169 H646 F644 F66 F65 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi HIgn
    Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv Opt Hbs Htail Hesc Hutf Hhex HFr HstateTail A0 A8 HdestTail B0 B8
    Hderef Vec HcontractTail Hob HD Hout Hhead HΦ

end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (body297Prologue prologue297)
open WNear.Binary.BalanceOfPresent (code293)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.ToVec
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
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_input_parser_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (lo hi : UInt64)
    (bs oldOpt optTail oldVec derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hbase : len = InitialState.memLen)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : RegOk 2048 len (some bs))
    (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF)
    (hFamily : PresentParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
    Cd ∗ inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        parseGas +
        presentParserSuccessCost cfg outF h S a lo hi R)))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceI n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
      n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
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
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((outF + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [.i32 (s + 88)] ((f297.body.drop 12).take 138) Φ := by
  iintro ⟨#HCd, #Hin, #F527, #HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, Hopt, HoptTail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 12).take 138 = [.call 527] ++ (f297.body.drop 13).take 137 := by rfl
  rw [hseg]
  iapply mwpi_seq
  icases stk_split n (s.toNat - 592) 432 160 $$ Hstk with ⟨Hlo, Hstk⟩
  ihave Hstk := stk_addr (show s.toNat - 592 + 432 = s.toNat - 160 by omega) $$ Hstk
  have hn := hm.mem
  have ha527 := hm.funcs 527 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have S527 := f527_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    s (s + 88) (by omega) hal (by simp [UInt32.toNat_add]; omega) idx 2048 len live oldOpt hopt h0
    (by simpa [hinput] using hinputLimit) (by simpa [hinput] using hok)
  mcall S527 using [Hg HI Hstk Hvt Hinv Hopt Hhost] with (mstep_norm_full; omega)
  · iunfold pre527
    iframe Hg HI Hstk Hvt Hinv Hopt Hhost
    ipureintro; rfl
  iunfold post527 at HQ
  rw [hinput, hafter]
  icases HQ with ⟨%hrs, Hg, HI, Hstk, Hvt, Hopt, Hhost⟩
  subst hrs
  iunfold optVecAt at Hopt
  icases Hopt with ⟨%ip, O0, O4, O8, %len', %⟨hip, hstep⟩, Hinv, Hbs⟩
  iunfold ifaceI at HI
  icases HI with ⟨HI, Hslot⟩
  ihave Hstk := stk_addr (show s.toNat - 160 = s.toNat - 592 + 432 by omega) $$ Hstk
  ihave Hstk := stk_join n (s.toNat - 592) 432 160 $$ [Hlo Hstk]
  · iframe Hlo Hstk
  have hpos : 0 < bs.length := hok.1
  have hnlen : (UInt32.ofNat bs.length).toNat = bs.length := by
    simp only [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hic : UInt32.ofNat bs.length ≠ 0 := by
    intro hz
    have hz' := congrArg UInt32.toNat hz
    rw [hnlen] at hz'
    simp at hz'
    simp [hz'] at hpos
  ihave Hinv := AllocZeroed.heapInv_bound n 2048 len' _ 1 $$ Hinv
  icases Hinv with ⟨%⟨hbound, hlen32⟩, Hinv⟩
  have hptr : ip.toNat + bs.length < 2 ^ 32 := by
    have hx := hbound ip.toNat bs.length (by simp)
    omega
  have hL' : len' = InitialState.memLen ∨ len' = grownLen InitialState.memLen (UInt32.ofNat bs.length) := by
    simpa only [hbase] using hstep
  ihave Htail : n ↦[wms][ ip.toNat + bs.length ] ([] : List UInt8) $$ []
  · iapply ScratchGrow.memBytes_nil
  have Hnext := provider_expect_deref_parser_through_cleanup_present cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    ip (UInt32.ofNat bs.length) idx len' a live 1 lo hi bs [] optTail oldVec derefOut parseGas outF Cd
    ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic hip
    (by simp [hnlen]) hoptTail holdVec hderef hlen hptr hL' hob hstateTail hcontractTail hdestTail hA hB hout hhead
    h S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hsome hreg ptr0 hret Φ hFamily
  iapply Hnext
  unfold cost527 at *
  simp only [hnlen]
  iframe HCd HC66 H169 H646 F644 F66 F65 F157 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456
    Hdrop F68 HIC Hi HIgn Hg HI Hstk Hvt Hstatekey Hhost Hinv O0 O4 O8 HoptTail Hbs Htail Hesc Hutf Hhex HFr
    HstateTail A0 A8 HdestTail B0 B8 Hderef Hvec HcontractTail Hob HD Hout Hhead
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro %p %c Hpost
  icases Hpost with ⟨Hc, P, L, Hesc, Hutf, Hhex, HFr, Hg, Hinv, Hhost⟩
  ispecialize HΦ $$ %p %c
  iapply HΦ $$ [Hc P L Hesc Hutf Hhex HFr Hg Hinv Hhost]
  simp only [List.cons_append, List.nil_append]
  iframe Hc L Hesc Hutf Hhex HFr Hg Hinv Hhost
  iexists ip
  iexact P

end WNear.Binary.BalanceOf297PresentCall


namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (body297Prologue prologue297)
open WNear.Binary.BalanceOfPresent (code293)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.ToVec
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
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_input_setup_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (lo hi : UInt64)
    (bs oldOpt optTail oldVec derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hbase : len = InitialState.memLen)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : RegOk 2048 len (some bs))
    (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF)
    (hFamily : PresentParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
    Cd ∗ inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        parseGas +
        presentParserSuccessCost cfg outF h S a lo hi R))))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceI n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
      n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
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
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((outF + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 9).take 141) Φ := by
  iintro ⟨#HCd, #Hin, #F527, #HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, Hopt, HoptTail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 9).take 141 =
      [.local_get 0, .i32_const 88, .i32_binop .add] ++ (f297.body.drop 12).take 138 := by rfl
  rw [hseg]
  iapply mwpi_seq
  mstep; mstep; mstep
  iapply (provider_input_parser_through_cleanup_present cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    idx len a live lo hi bs oldOpt optTail oldVec derefOut parseGas outF Cd ob stateTail contractTail destTail out head
    oldA oldB oldC oldD hs hal hframe hopt hoptTail holdVec hderef hlen hbase hob hstateTail hcontractTail hdestTail hA hB hout hhead h0 h hinput hafter hinputLimit hok
    S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hsome hreg ptr0 hret Φ hFamily)
  simp only [List.cons_append, List.nil_append]
  iframe HCd Hin F527 HC66 H169 H646 F644 F66 F65 F157 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456
    Hdrop F68 HIC Hi HIgn Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv Hopt HoptTail Hesc Hutf Hhex HFr HstateTail
    A0 A8 HdestTail B0 B8 Hderef Hvec HcontractTail Hob HD Hout Hhead HΦ

end WNear.Binary.BalanceOf297PresentCall


namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (body297Prologue prologue297)
open WNear.Binary.BalanceOfPresent (code293)
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
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_present_body (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (lo hi : UInt64)
    (bs oldOpt optTail oldVec derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 < 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hbase : len = InitialState.memLen)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : RegOk 2048 len (some bs))
    (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF)
    (hFamily : PresentParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
    Cd ∗ codeA inst mi A ∗ inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        parseGas +
        presentParserSuccessCost cfg outF h S a lo hi R)))))) ∗
      g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ stk n (s.toNat - 592) 592 ∗
      hookCells n 0 hookOld 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
      n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ ta ↦[wt][ 44 ] Ref.func (A 246) ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
      n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
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
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((outF + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d ⟨#[.i32 0, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩ [] f297.body Φ := by
  iintro ⟨#HCd, #HA, #Hin, #F527, #HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, Hstk, Hhook, Hsetupkey, T116, T106,
    HB, HV, V36, T44, Hvt, Hstatekey, Hhost, Hinv, Hopt, HoptTail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hsp : (s + 160).toNat = s.toNat + 160 := by simp [UInt32.toNat_add]; have := s.toNat_lt; omega
  have hrestore : s + 160 - 160 = s := by simp
  have hseg : f297.body = body297Prologue ++ (f297.body.drop 9).take 141 := by rfl
  rw [hseg]
  icases stk_split n (s.toNat - 592) 512 80 $$ Hstk with ⟨Hlo, Htop⟩
  ihave Htop := stk_addr (show s.toNat - 592 + 512 = (s + 160).toNat - 240 by omega) $$ Htop
  iapply (prologue297 cfg lim d inst mi A n g ta hm (by omega) Cg
    (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 +
      (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        parseGas +
        presentParserSuccessCost cfg outF h S a lo hi R)))))
    gt (s + 160) x1 x2 x3 (by omega) (by rw [hsp]; omega) hookOld k3 ((f297.body.drop 9).take 141) Φ)
  iframe HA Hc Hg Htop Hhook Hsetupkey T116 T106 HB HV V36 T44
  iintro Hc Hg Htop HI
  rw [hrestore]
  ihave Htop := stk_addr (show (s + 160).toNat - 240 = s.toNat - 592 + 512 by omega) $$ Htop
  ihave Hstk := stk_join n (s.toNat - 592) 512 80 $$ [Hlo Htop]
  · iframe Hlo Htop
  have Hsuffix := provider_input_setup_through_cleanup_present (GF := GF) cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    idx len a live lo hi bs oldOpt optTail oldVec derefOut parseGas outF Cd ob stateTail contractTail destTail out head
    oldA oldB oldC oldD hs hal (by omega) hopt hoptTail holdVec hderef hlen hbase hob hstateTail hcontractTail hdestTail hA hB hout hhead h0 h hinput hafter hinputLimit hok
    S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hsome hreg ptr0 hret Φ hFamily
  simp only [frame] at Hsuffix
  iapply Hsuffix
  simp only [frame]
  iframe HCd Hin F527 HC66 H169 H646 F644 F66 F65 F157 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456
    Hdrop F68 HIC Hi HIgn Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv Hopt HoptTail Hesc Hutf Hhex HFr HstateTail
    A0 A8 HdestTail B0 B8 Hderef Hvec HcontractTail Hob HD Hout Hhead HΦ

end WNear.Binary.BalanceOf297PresentCall


namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.Interface (IfaceMod)
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
section Resource
variable {GF : BundledGFunctors} [WasmGS NearState GF]
theorem ledger_parser_family_present (cfg : WasmConfig) (lim : ExecLimits) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (gt : GlobalType)
    (bs rest : List UInt8) (a : WNear.AccountId) (N F : Nat) (K646 K169 K81 : Nat → Nat)
    (hlen : bs.length ≤ 4194304) (hF : 1 ≤ F)
    (hkeys : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyRoomCharges cfg 2048 bs (Ledger bs len F false) K646)
    (hkeysSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      KeyRoomCharges cfg 2048 bs (Ledger bs len F true) K646)
    (hvalues : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      ValueRoomCharges cfg 2048 bs (Ledger bs len F false) K169)
    (hignored : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg bs K81 (Ledger bs len F false))
    (hignoredSaved : ∀ len, len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length) →
      IgnoreCharges cfg bs K81 (Ledger bs len F true))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length) :
    BalanceOf297PresentCall.PresentParserFamily (GF := GF) cfg lim inst mi A n g ta gt bs a F
      (ledgerParserCost cfg K646 K169 K81 bs rest N) (F + 43) (ledgerParserCode n inst mi A) := by
  intro Cg d sp out ptr idx ob len live hd hob hout _ hptr hsp hal hL
  exact ledger_parser_contract_present cfg lim d inst mi A n g ta Cg hm gt sp out ptr idx ob bs rest a N len F live
    hd hob hout hlen hptr hsp hal K646 K169 K81 (input_ledger_bounds bs len F hlen hF hL)
    (hkeys len hL) (hkeysSaved len hL) (hvalues len hL) (hignored len hL) (hignoredSaved len hL) ho hloop hend


end Resource
end WNear.Binary.SerdeObjectMixedTrace

/-! Actual-code parser providers, whole-method resource composition and receipt refinement.
The general provider and model-budget obligations remain explicit. -/

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (initial_memory_room code297 code297Input code297Parser code297Lookup code297Return)
open WNear.Binary.BalanceOfPresent (code293)
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

variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_present_body_initial_resources (runtime : RuntimeConfig) (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (hlen : bs.length < 2 ^ 24)
    (hpos : 0 < bs.length)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true)
    (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF)
    (hp : PresentParserFamily cfg lim 0 wInst id 0 0 0 InitialState.g0.type bs a 1 parseGas outF Cd) :
    Cd ∗ code297 runtime.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗ SerdeIgnValue.code81 0 wInst id ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        parseGas +
        presentParserSuccessCost cfg outF h S a lo hi R)))))) ∗
      0 ↦[wg] InitialState.g0 ∗ InitialState.frame297 0 ∗
      FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 InitialState.memLen ∗
      0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics 0 ∗ mhostPt h0 ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        (∃ ip : UInt32, 0 ↦[i32][ ((1048416 : UInt32) + 24).toNat ] ip) ∗
        0 ↦[i32][ ((1048416 : UInt32) + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics 0 ∗ 0 ↦[wg] InitialState.g0 ∗ (∃ hl, heapInv 0 2048 hl [] (((((outF + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame 0 wInst (1048416 : UInt32) (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) ((1048416 : UInt32) + 40))) ⊢
    mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ [] f297.body Φ := by
  iintro ⟨#HCd, HC, HIgn, C, Hg, HF, HS, V36, T44, ESC, UTF, HEX, HFr, HH, HK⟩
  have hr := initial_memory_room bs hlen
  have hok : RegOk 2048 InitialState.memLen (some bs) := by
    obtain ⟨ha, hp, hm, hw⟩ := hr
    refine ⟨hpos, by omega, ha, hp, ?_, ?_⟩ <;> omega
  have hbody := provider_present_body cfg lim d 0 runtime.fees.numExtraBytesRecord wInst id 0 0 0
    (some 2048) Interface.wInst_ifaceMod hd Cg R InitialState.g0.type 1048416 0 0 0 123 InitialState.memLen a [] lo hi bs
    (List.replicate 12 0) (List.replicate 4 0) (List.replicate 12 0) (List.replicate 8 0) parseGas outF Cd
    (List.replicate 16 0) (List.replicate 24 0) (List.replicate 28 0) (List.replicate 4 0)
    (List.replicate 12 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) 0 0 0 0
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    hlen rfl  (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) h0 h hinput hafter hinputLimit hok S st hv hacc hlim
    hcanon hlink bud hproof hbudget hlimAccount hsome hreg 1051836 hret Φ hp
  rw [show (⟨InitialState.g0.type, .i32 ((1048416 : UInt32) + 160)⟩ : GlobalInst) = InitialState.g0 by simp [InitialState.g0]] at hbody
  simp only [id] at hbody
  rw [show WNear.Binary.BalanceOfPresent.code293 runtime.fees.numExtraBytesRecord 0 2048 0 wInst id (some 2048) = WNear.Binary.BalanceOfAbsent.code293 runtime.fees.numExtraBytesRecord 0 2048 0 wInst id (some 2048) from rfl] at hbody
  iapply hbody
  iunfold code297 at HC
  icases HC with ⟨HI, HP, HL, HR, HIF, HINST⟩
  iunfold code297Input at HI
  icases HI with ⟨HI0, HI1, HI2⟩
  iunfold code297Parser at HP
  icases HP with ⟨HP0, HP1, HP2, HP3, HP4, HP5, HP6⟩
  iunfold code297Lookup at HL
  icases HL with ⟨HL0, HL1, HL2, HL3, HL4, HL5⟩
  iunfold code297Return at HR
  icases HR with ⟨HR0, HR1, HR2, HR3, HR4, HR5, HR6, HR7⟩
  iunfold InitialState.frame297 at HF
  icases HF with ⟨STK, HEAD, OB, DEREF, B, D, VEC, CT, OPT, OT, ST, A, AC, DT, OUT, -⟩
  iunfold FtTotalSupply.statics at HS
  icases HS with ⟨HOOK, LK, T116, T106, BC, VTAB, VT, HEAP, KEY, TV⟩
  simp [id, List.cons_append, List.nil_append]
  iframe HCd C Hg V36 T44 ESC UTF HEX HFr HH HK HIgn HIF HINST HI0 HI1 HI2 HP0 HP1 HP2 HP3 HP4 HP5 HP6 HL0 HL1 HL2 HL3 HL4 HL5 HR0 HR1 HR2 HR3 HR4 HR5 HR6 HR7 STK HEAD OB DEREF B D VEC CT OPT OT ST A AC DT OUT HOOK LK T116 T106 BC VTAB VT HEAP KEY TV

end WNear.Binary.BalanceOf297PresentCall
