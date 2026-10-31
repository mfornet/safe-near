import Bridge.Functions.BalanceOf297NoneCall
import Bridge.Functions.BalanceOf297ParserFamily
import Bridge.Methods.FtBalanceOfProviderInitial

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateReadLenF (stateCodeF)
open WNear.Binary.FtTotalSupply (ReadNone staticsP codeP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.BalanceOf297AbsentCall (frame ParserCallContract parser_fixed_resources)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- A successful deployed parser provider feeds the uninitialized trap, preserving the exact named provider premise. -/
theorem provider_none_panics (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 18 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail parserOut : List UInt8) (parseGas outF : Nat) (Cd Fr : IProp GF) [Persistent Cd]
    (stateTail oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
    (hstateTail : stateTail.length = 24) (hA : oldA.length = 8) (hB : oldB.length = 8)
    (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF)
    (hParser : ParserCallContract cfg lim (d + 1) inst mi A n g ta Cg gt s (s + 88) ip idx
      parserOut bs a len ((ip.toNat, ic.toNat) :: live) F parseGas outF Cd Fr) :
    Cd ∗ A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗
      stateCodeF e inst mi A n 2048 (some 2048) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ ifaceCode e inst mi A n (some 2048) ∗
      codeP e inst mi A ∗ inst ↪[inst] mi ∗ dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (1000 * cfg.regularOpCost + parseGas +
        (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗ n ↦[wms][ (s + 88).toNat ] parserOut ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ∗ n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[i32][ (s + 48).toNat ] ip ∗ n ↦[i32][ (s + 48).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 48).toNat + 8 ] UInt32.ofNat bs.length ∗ staticsP n ta A ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3)
        [.i32 (s + 88), .i32 ip, .i32 (UInt32.ofNat bs.length)] ((f297.body.drop 35).take 115) Φ := by
  iintro ⟨#HCd, #F65, #HSC, #F219, #F155, #HIC, #HP, #Hi, #Hdrop, #F68, Hc,
    Hg, HI, Hstk, Hvt, Hstatekey, Hhost, Hinv, HparserOut, Hbs, Htail, Hesc, Hutf, Hhex, HFr,
    HstateTail, A0, A8, B0, B8, I0, I4, I8, HSP, W⟩
  have hseg : (f297.body.drop 35).take 115 = [.call 65] ++ (f297.body.drop 36).take 114 := by rfl
  rw [hseg]
  iapply mwpi_seq
  icases stk_split n (s.toNat - 592) 144 448 $$ Hstk with ⟨Hlo, Hstk⟩
  ihave Hstk := stk_addr (show s.toNat - 592 + 144 = s.toNat - 448 by omega) $$ Hstk
  have hn := hm.mem
  have ha65 := hm.funcs 65 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have hs65 := hParser
  unfold ParserCallContract at hs65
  ihave #S65 := hs65 $$ HCd
  mcall S65 using [Hg Hstk Hvt Hinv HparserOut Hbs Hesc Hutf Hhex HFr]
    with (mstep_norm_full; omega)
  · iframe Hg Hstk Hvt Hinv HparserOut Hbs Hesc Hutf Hhex HFr
  icases HQ with ⟨%hrs, Hg, Hstk, Hvt, Hbs, Hesc, Hutf, Hhex, HFr, %len', %hroom', Hparser⟩
  subst hrs
  ihave Hstk := stk_addr (show s.toNat - 448 = s.toNat - 592 + 144 by omega) $$ Hstk
  ihave Hstk := stk_join n (s.toNat - 592) 144 448 $$ [Hlo Hstk]
  · iframe Hlo Hstk
  ihave Hinput := BorshFT.joinB (n := n) (a := ip.toNat) (b := ip.toNat + bs.length) bs tail rfl $$ [Hbs Htail]
  · iframe Hbs Htail
  ihave Hblock : block n ip.toNat ic.toNat $$ [Hinput]
  · iunfold block
    iexists bs ++ tail
    iframe Hinput
    ipureintro; simp [hinput]
  ihave Hparser := parser_fixed_resources n (s + 88) a ip ic live len' outF $$ Hparser
  icases Hparser with ⟨%p, %c, %rest, %⟨hc, hkey, hrest, hL, hp⟩, Tag, P, C, L0, Hkey, Hrest, Hinv⟩
  iapply (parsed_none_panics cfg lim d inst e mi A n g ta hm hd Cg R gt s x1 x2 x3
    p c (UInt32.ofNat a.val.utf8ByteSize) ip ic (UInt32.ofNat bs.length) idx 2048 len' live outF
    stateTail oldA oldB oldC oldD hs hal hframe hstateTail hA hB hic h st hr Φ)
  iframe HSC F219 F155 HIC HP Hi Hdrop F68 Hg HI Hstk Hvt Hstatekey Hhost
    Tag P C L0 HstateTail A0 A8 B0 B8 I0 I4 I8 Hblock Hinv HSP W
  iapply BorrowMut.credits_le
  iframe Hc
  ipureintro; omega
end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateReadLenF (stateCodeF)
open WNear.Binary.FtTotalSupply (ReadNone staticsP codeP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.BalanceOf297AbsentCall (frame ParserCallContract parser_fixed_resources)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- A successful deployed parser provider feeds the uninitialized trap, preserving the exact named provider premise. -/
theorem deref_provider_none_panics (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 46 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail parserOut derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (stateTail oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
    (hparserOut : parserOut.length = 16) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (hL : len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (hstateTail : stateTail.length = 24) (hA : oldA.length = 8) (hB : oldB.length = 8)
    (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF)
    (hFamily : BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd) :
    Cd ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗
      stateCodeF e inst mi A n 2048 (some 2048) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ ifaceCode e inst mi A n (some 2048) ∗
      codeP e inst mi A ∗ inst ↪[inst] mi ∗ dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
        (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗ n ↦[wms][ (s + 88).toNat ] parserOut ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] (bytes32 ip ++ (bytes32 ic ++ bytes32 (UInt32.ofNat bs.length))) ∗ staticsP n ta A ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3)
        [] ((f297.body.drop 21).take 129) Φ := by
  iintro ⟨#HCd, #F779, #F65, #HSC, #F219, #F155, #HIC, #HP, #Hi, #Hdrop, #F68, Hc,
    Hg, HI, Hstk, Hvt, Hstatekey, Hhost, Hinv, HparserOut, Hbs, Htail, Hesc, Hutf, Hhex, HFr,
    HstateTail, A0, A8, B0, B8, Hderef, Hvec, HSP, W⟩
  have hseg : (f297.body.drop 21).take 129 =
      (f297.body.drop 21).take 14 ++ (f297.body.drop 35).take 115 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (BalanceOf297AbsentCall.deref_and_parser_setup cfg lim d inst mi A n hm.mem (hm.funcs 779 (by decide)) (by omega) Cg
    (1000 * cfg.regularOpCost + parseGas +
      (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)))
    s x1 x2 x3 ip ic (UInt32.ofNat bs.length) derefOut hderef hframe)
  iframe Hi F779 Hc Hderef Hvec
  inext
  iintro ⟨Hc, P, L, Hvec⟩
  icases BorshFT.splitB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 4)
    (bytes32 ip) (bytes32 ic ++ bytes32 (UInt32.ofNat bs.length)) (by simp) $$ Hvec with ⟨I0, Irest⟩
  icases BorshFT.split64' (n := n) (a := (s + 48).toNat + 4) (b := (s + 48).toNat + 8)
    ic (UInt32.ofNat bs.length) (by omega) $$ Irest with ⟨I4, I8⟩
  have hParser := hFamily Cg (d + 1) s (s + 88) ip idx parserOut len
    ((ip.toNat, ic.toNat) :: live) (by omega) hparserOut
    (by simp [UInt32.toNat_add]; omega) hlen hptr (by omega) hal hL
  simp only [Post.mseq_normal]
  iapply (provider_none_panics cfg lim d inst e mi A n g ta hm (by omega) Cg R gt s x1 x2 x3
    ip ic idx len a live F bs tail parserOut parseGas outF Cd (SerdeObjectNoEsc.parserStatics n)
    stateTail oldA oldB oldC oldD hs hal hframe hic hinput hstateTail hA hB h st hr Φ hParser)
  iframe HCd F65 HSC F219 F155 HIC HP Hi Hdrop F68 Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv
    HparserOut Hbs Htail Hesc Hutf Hhex HFr HstateTail A0 A8 B0 B8 I0 I4 I8 HSP W
end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateReadLenF (stateCodeF)
open WNear.Binary.FtTotalSupply (ReadNone staticsP codeP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.BalanceOf297AbsentCall (frame ParserCallContract parser_fixed_resources)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- A successful deployed parser provider feeds the uninitialized trap, preserving the exact named provider premise. -/
theorem expect_provider_none_panics (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 46 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail optTail oldVec derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (stateTail oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hinput : bs.length + tail.length = ic.toNat)
    (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hip : ip ≠ 0) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (hL : len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (hstateTail : stateTail.length = 24) (hA : oldA.length = 8) (hB : oldB.length = 8)
    (h : NearState) (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF)
    (hFamily : BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a F parseGas outF Cd) :
    Cd ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗
      stateCodeF e inst mi A n 2048 (some 2048) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ ifaceCode e inst mi A n (some 2048) ∗
      codeP e inst mi A ∗ inst ↪[inst] mi ∗ dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
        (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R))))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗ n ↦[i32][ (s + 88).toNat ] ip ∗ n ↦[i32][ (s + 88).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 88).toNat + 8 ] UInt32.ofNat bs.length ∗ n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] oldVec ∗ staticsP n ta A ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3)
        [] ((f297.body.drop 13).take 137) Φ := by
  iintro ⟨#HCd, #F157, #F779, #F65, #HSC, #F219, #F155, #HIC, #HP, #Hi, #Hdrop, #F68, Hc,
    Hg, HI, Hstk, Hvt, Hstatekey, Hhost, Hinv, O0, O4, O8, HoptTail, Hbs, Htail, Hesc, Hutf, Hhex, HFr,
    HstateTail, A0, A8, B0, B8, Hderef, Hvec, HSP, W⟩
  have hseg : (f297.body.drop 13).take 137 =
      (f297.body.drop 13).take 8 ++ (f297.body.drop 21).take 129 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (BalanceOf297AbsentCall.input_expect cfg lim d inst mi A n hm.mem (hm.funcs 157 (by decide)) (by omega) Cg
    (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
      (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R))))
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
  iapply (deref_provider_none_panics cfg lim d inst e mi A n g ta hm hd Cg R gt s x1 x2 x3
    ip ic idx len a live F bs tail (((bytes32 ip ++ bytes32 ic) ++ bytes32 (UInt32.ofNat bs.length)) ++ optTail)
    derefOut parseGas outF Cd stateTail oldA oldB oldC oldD hs hal hframe hic hinput
    (by simp [bytes32_length, hoptTail]) hderef hlen hptr hL hstateTail hA hB h st hr Φ hFamily)
  simp only [List.append_assoc] at *
  iframe HCd F779 F65 HSC F219 F155 HIC HP Hi Hdrop F68 Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv
    Opt Hbs Htail Hesc Hutf Hhex HFr HstateTail A0 A8 B0 B8 Hderef Vec HSP W
end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateReadLenF (stateCodeF)
open WNear.Binary.FtTotalSupply (ReadNone staticsP codeP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.BalanceOf297AbsentCall (frame ParserCallContract parser_fixed_resources)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.EnvInput (inCode pre527 post527 ifaceI cost527 f527_spec)
open WNear.Binary.ReadRegister (RegOk optVecAt)
open WNear.Binary.VecFromElem (grownLen)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- A successful deployed parser provider feeds the uninitialized trap, preserving the exact named provider premise. -/
theorem input_provider_none_panics (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 46 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat))
    (bs oldOpt optTail oldVec derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (stateTail oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hbase : len = InitialState.memLen)
    (h0 : NearState) (hinput : h0.context.input = bs)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : ReadRegister.RegOk 2048 len (some bs))
    (hstateTail : stateTail.length = 24) (hA : oldA.length = 8) (hB : oldB.length = 8)
    (h : NearState) (hafter : inputHost h0 0 = h) (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF)
    (hFamily : BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
    Cd ∗ EnvInput.inCode e inst mi A n 2048 (some 2048) ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗
      stateCodeF e inst mi A n 2048 (some 2048) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ ifaceCode e inst mi A n (some 2048) ∗
      codeP e inst mi A ∗ inst ↪[inst] mi ∗ dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (100 * cfg.regularOpCost + EnvInput.cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
        (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)))))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceI n ta A ∗ stk n (s.toNat - 592) 592 ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗ n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] oldVec ∗ staticsP n ta A ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3)
        [.i32 (s + 88)] ((f297.body.drop 12).take 138) Φ := by
  iintro ⟨#HCd, #Hin, #F527, #F157, #F779, #F65, #HSC, #F219, #F155, #HIC, #HP, #Hi, #Hdrop, #F68, Hc,
    Hg, HI, Hstk, Hvt, Hstatekey, Hhost, Hinv, Hopt, HoptTail, Hesc, Hutf, Hhex, HFr,
    HstateTail, A0, A8, B0, B8, Hderef, Hvec, HSP, W⟩
  have hseg : (f297.body.drop 12).take 138 = [.call 527] ++ (f297.body.drop 13).take 137 := by rfl
  rw [hseg]
  iapply mwpi_seq
  icases stk_split n (s.toNat - 592) 432 160 $$ Hstk with ⟨Hlo, Hstk⟩
  ihave Hstk := stk_addr (show s.toNat - 592 + 432 = s.toNat - 160 by omega) $$ Hstk
  have hn := hm.mem
  have ha527 := hm.funcs 527 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have S527 := f527_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta (some 2048) hm (by omega) Cg gt
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
  iapply (expect_provider_none_panics cfg lim d inst e mi A n g ta hm hd Cg R gt s x1 x2 x3
    ip (UInt32.ofNat bs.length) idx len' a live 1 bs [] optTail oldVec derefOut parseGas outF Cd
    stateTail oldA oldB oldC oldD hs hal hframe hic (by simp [hnlen]) hoptTail holdVec hip hderef
    hlen hptr hL' hstateTail hA hB h st hr Φ hFamily)
  unfold cost527 at *
  simp only [hnlen]
  iframe HCd F157 F779 F65 HSC F219 F155 HIC HP Hi Hdrop F68 Hg HI Hstk Hvt Hstatekey Hhost Hinv
    O0 O4 O8 HoptTail Hbs Htail Hesc Hutf Hhex HFr HstateTail A0 A8 B0 B8 Hderef Hvec HSP W
  iapply BorrowMut.credits_le
  iframe Hc
  ipureintro; omega
end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateReadLenF (stateCodeF)
open WNear.Binary.FtTotalSupply (ReadNone staticsP codeP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.BalanceOf297AbsentCall (frame ParserCallContract parser_fixed_resources)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.EnvInput (inCode pre527 post527 ifaceI cost527 f527_spec)
open WNear.Binary.ReadRegister (RegOk optVecAt)
open WNear.Binary.VecFromElem (grownLen)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- A successful deployed parser provider feeds the uninitialized trap, preserving the exact named provider premise. -/
theorem input_setup_provider_none_panics (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 46 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat))
    (bs oldOpt optTail oldVec derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (stateTail oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hbase : len = InitialState.memLen)
    (h0 : NearState) (hinput : h0.context.input = bs)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : ReadRegister.RegOk 2048 len (some bs))
    (hstateTail : stateTail.length = 24) (hA : oldA.length = 8) (hB : oldB.length = 8)
    (h : NearState) (hafter : inputHost h0 0 = h) (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF)
    (hFamily : BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
    Cd ∗ EnvInput.inCode e inst mi A n 2048 (some 2048) ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗
      stateCodeF e inst mi A n 2048 (some 2048) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ ifaceCode e inst mi A n (some 2048) ∗
      codeP e inst mi A ∗ inst ↪[inst] mi ∗ dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + EnvInput.cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
        (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R))))))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceI n ta A ∗ stk n (s.toNat - 592) 592 ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗ n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] oldVec ∗ staticsP n ta A ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3)
        [] ((f297.body.drop 9).take 141) Φ := by
  iintro ⟨#HCd, #Hin, #F527, #F157, #F779, #F65, #HSC, #F219, #F155, #HIC, #HP, #Hi, #Hdrop, #F68, Hc,
    Hg, HI, Hstk, Hvt, Hstatekey, Hhost, Hinv, Hopt, HoptTail, Hesc, Hutf, Hhex, HFr,
    HstateTail, A0, A8, B0, B8, Hderef, Hvec, HSP, W⟩
  have hseg : (f297.body.drop 9).take 141 =
      [.local_get 0, .i32_const 88, .i32_binop .add] ++ (f297.body.drop 12).take 138 := by rfl
  rw [hseg]
  iapply mwpi_seq
  mstep; mstep; mstep
  iapply (input_provider_none_panics cfg lim d inst e mi A n g ta hm hd Cg R gt s x1 x2 x3
    idx len a live bs oldOpt optTail oldVec derefOut parseGas outF Cd stateTail oldA oldB oldC oldD
    hs hal hframe hopt hoptTail holdVec hderef hlen hbase h0 hinput hinputLimit hok
    hstateTail hA hB h hafter st hr Φ hFamily)
  iframe HCd Hin F527 F157 F779 F65 HSC F219 F155 HIC HP Hi Hdrop F68 Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv
    Hopt HoptTail Hesc Hutf Hhex HFr HstateTail A0 A8 B0 B8 Hderef Hvec HSP W
end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateReadLenF (stateCodeF)
open WNear.Binary.FtTotalSupply (ReadNone staticsP codeP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.BalanceOf297AbsentCall (frame ParserCallContract parser_fixed_resources)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.EnvInput (inCode pre527 post527 ifaceI cost527 f527_spec)
open WNear.Binary.ReadRegister (RegOk optVecAt)
open WNear.Binary.VecFromElem (grownLen)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- A successful deployed parser provider feeds the uninitialized trap, preserving the exact named provider premise. -/
theorem provider_none_body (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 46 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat))
    (bs oldOpt optTail oldVec derefOut : List UInt8) (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd]
    (stateTail oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 < 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hbase : len = InitialState.memLen)
    (h0 : NearState) (hinput : h0.context.input = bs)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : ReadRegister.RegOk 2048 len (some bs))
    (hstateTail : stateTail.length = 24) (hA : oldA.length = 8) (hB : oldB.length = 8)
    (h : NearState) (hafter : inputHost h0 0 = h) (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF)
    (hFamily : BalanceOf297AbsentCall.ParserFamily cfg lim inst mi A n g ta gt bs a 1 parseGas outF Cd) :
    Cd ∗ FtTotalSupply.codeA inst mi A ∗ EnvInput.inCode e inst mi A n 2048 (some 2048) ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗ A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗
      stateCodeF e inst mi A n 2048 (some 2048) ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ ifaceCode e inst mi A n (some 2048) ∗
      codeP e inst mi A ∗ inst ↪[inst] mi ∗ dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + EnvInput.cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
        (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)))))))) ∗
      g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ stk n (s.toNat - 592) 592 ∗
      SetupPanicHook.hookCells n 0 hookOld 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      SetBlockchainInterface.blockchainInterfaceCells n 0 0 0 k3 ∗ FtTotalSupply.vtab n ta A ∗
      n ↦[wms][ 1050188 + 36 ] Interface.dataWord (1050188 + 36) ∗ ta ↦[wt][ 44 ] Ref.func (A 246) ∗ vt n 1057464 idx ta (A 578) ∗
      n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗ n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] oldVec ∗ staticsP n ta A ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩ [] f297.body Φ := by
  iintro ⟨#HCd, #HA, #Hin, #F527, #F157, #F779, #F65, #HSC, #F219, #F155, #HIC, #HP, #Hi, #Hdrop, #F68, Hc,
    Hg, Hstk, Hhook, Hsetupkey, T116, T106, HB, HV, V36, T44, Hvt, Hstatekey, Hhost, Hinv,
    Hopt, HoptTail, Hesc, Hutf, Hhex, HFr, HstateTail, A0, A8, B0, B8, Hderef, Hvec, HSP, W⟩
  have hsp : (s + 160).toNat = s.toNat + 160 := by simp [UInt32.toNat_add]; have := s.toNat_lt; omega
  have hrestore : s + 160 - 160 = s := by simp
  have hseg : f297.body = BalanceOf297AbsentCall.body297Prologue ++ (f297.body.drop 9).take 141 := by rfl
  rw [hseg]
  icases stk_split n (s.toNat - 592) 512 80 $$ Hstk with ⟨Hlo, Htop⟩
  ihave Htop := stk_addr (show s.toNat - 592 + 512 = (s + 160).toNat - 240 by omega) $$ Htop
  iapply (BalanceOf297AbsentCall.prologue297 cfg lim d inst mi A n g ta hm (by omega) Cg
    (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 +
      (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
        (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)))))))
    gt (s + 160) x1 x2 x3 (by omega) (by rw [hsp]; omega) hookOld k3 ((f297.body.drop 9).take 141) Φ)
  iframe HA Hc Hg Htop Hhook Hsetupkey T116 T106 HB HV V36 T44
  iintro Hc Hg Htop HI
  rw [hrestore]
  ihave Htop := stk_addr (show (s + 160).toNat - 240 = s.toNat - 592 + 512 by omega) $$ Htop
  ihave Hstk := stk_join n (s.toNat - 592) 512 80 $$ [Hlo Htop]
  · iframe Hlo Htop
  have Hsuffix := input_setup_provider_none_panics (GF := GF) cfg lim d inst e mi A n g ta hm hd Cg R gt s x1 x2 x3
    idx len a live bs oldOpt optTail oldVec derefOut parseGas outF Cd stateTail oldA oldB oldC oldD
    hs hal (by omega) hopt hoptTail holdVec hderef hlen hbase h0 hinput hinputLimit hok
    hstateTail hA hB h hafter st hr Φ hFamily
  simp only [frame] at Hsuffix
  iapply Hsuffix
  iframe HCd Hin F527 F157 F779 F65 HSC F219 F155 HIC HP Hi Hdrop F68 Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv
    Hopt HoptTail Hesc Hutf Hhex HFr HstateTail A0 A8 B0 B8 Hderef Hvec HSP W
end WNear.Binary.BalanceOf297NoneCall

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_addr)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.StateReadLenF (stateCodeF)
open WNear.Binary.FtTotalSupply (ReadNone staticsP codeP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.BalanceOf297AbsentCall (frame ParserCallContract parser_fixed_resources)
variable {GF : BundledGFunctors} [WasmGS NearState GF]
open WNear.Binary.EnvInput (inCode pre527 post527 ifaceI cost527 f527_spec)
open WNear.Binary.ReadRegister (RegOk optVecAt)
open WNear.Binary.VecFromElem (grownLen)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Initial function-297 resources compose its entire uninitialized success-parser path. -/
theorem provider_none_body_initial_resources (runtime : RuntimeConfig) (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (a : WNear.AccountId) (bs : List UInt8)
    (parseGas outF : Nat) (Cd : IProp GF) [Persistent Cd] (hlen : bs.length < 2 ^ 24) (hpos : 0 < bs.length)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true)
    (st : Near.TrieOverlay.State) (hr : ReadNone h st) (Φ : Post NearState GF)
    (hp : BalanceOf297AbsentCall.ParserFamily cfg lim 0 wInst id 0 0 0 InitialState.g0.type bs a 1 parseGas outF Cd) :
    Cd ∗ BalanceOf297AbsentCall.code297 runtime.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗
      FtTotalSupply.codeP runtime.fees.numExtraBytesRecord 0 wInst id ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 +
        (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
          (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31 + R)))))))) ∗
      0 ↦[wg] InitialState.g0 ∗ InitialState.frame297 0 ∗
      FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 InitialState.memLen ∗ FtTotalSupply.staticsP 0 0 id ∗
      0 ↦[wms][ 1050188 + 36 ] Interface.dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics 0 ∗ mhostPt h0 ∗
      (∀ h1, ⌜StorageReadPost h StateRead.stateKey 0 st h1⌝ -∗ panicked Cg h1 notInit -∗ Φ.trap)
      ⊢ mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ [] f297.body Φ := by
  iintro ⟨#HCd, HC, #HP, C, Hg, HF, HS, HSP, V36, T44, ESC, UTF, HEX, HFr, HH, HK⟩
  have room := BalanceOf297AbsentCall.initial_memory_room bs hlen
  have hok : RegOk 2048 InitialState.memLen (some bs) := by
    obtain ⟨ha, hp, hm, hw⟩ := room
    refine ⟨hpos, by omega, ha, hp, ?_, ?_⟩ <;> omega
  have hbody := provider_none_body cfg lim d 0 runtime.fees.numExtraBytesRecord wInst id 0 0 0
    Interface.wInst_ifaceMod hd Cg R InitialState.g0.type 1048416 0 0 0 123 InitialState.memLen a [] bs
    (List.replicate 12 0) (List.replicate 4 0) (List.replicate 12 0) (List.replicate 8 0) parseGas outF Cd
    (List.replicate 24 0) (List.replicate 8 0) (List.replicate 8 0) 0 0 0 0
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp) hlen rfl
    h0 hinput hinputLimit hok (by simp) (by simp) (by simp) h hafter st hr Φ hp
  rw [show (⟨InitialState.g0.type, .i32 ((1048416 : UInt32) + 160)⟩ : GlobalInst) = InitialState.g0 by
    simp [InitialState.g0]] at hbody
  simp only [id] at hbody
  iapply hbody
  iunfold BalanceOf297AbsentCall.code297 at HC
  icases HC with ⟨HI, HP, HL, HR, HIF, HINST⟩
  iunfold BalanceOf297AbsentCall.code297Input at HI
  icases HI with ⟨HI0, HI1, HI2⟩
  iunfold BalanceOf297AbsentCall.code297Parser at HP
  icases HP with ⟨HP0, HP1, HP2, HP3, HP4, HP5, HP6⟩
  iunfold BalanceOf297AbsentCall.code297Lookup at HL
  icases HL with ⟨HL0, HL1, HL2, HL3, HL4, HL5⟩
  iunfold BalanceOf297AbsentCall.code297Return at HR
  icases HR with ⟨HR0, HR1, HR2, HR3, HR4, HR5, HR6, HR7⟩
  iunfold InitialState.frame297 at HF
  icases HF with ⟨STK, HEAD, OB, DEREF, B, D, VEC, CT, OPT, OT, ST, A, AC, DT, OUT, -⟩
  iunfold FtTotalSupply.statics at HS
  icases HS with ⟨HOOK, LK, T116, T106, BC, VTAB, VT, HEAP, KEY, TV⟩
  simp [id, List.cons_append, List.nil_append]
  iframe HCd HP C Hg HSP V36 T44 ESC UTF HEX HFr HH HK HIF HINST HI0 HI1 HI2 HP5 HP6 HL0 HL1 HL2
    HR3 HR6 HR7 STK DEREF B D VEC OPT OT ST A AC HOOK LK T116 T106 BC VTAB VT HEAP KEY

end WNear.Binary.BalanceOf297NoneCall
