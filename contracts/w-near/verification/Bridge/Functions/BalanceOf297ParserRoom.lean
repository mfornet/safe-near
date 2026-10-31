import Bridge.Functions.BalanceOf297InitialRoomCompose
import Bridge.Functions.StrRoom
import Bridge.Methods.InitialState

/-! Derive the copied-array parser room from one numerical initial page allowance. -/
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
/-- An input allocation consumes at most its charged pages, preserving the tail allowance. -/
theorem room_after_input_pages {pages tail len len' maxP : Nat}
    (hr : HeapRoomK (pages + tail) len maxP)
    (hh : len' = len ∨ len' = len + pages * 65536) : HeapRoomK tail len' maxP := by
  rcases hh with hh | hh
  · subst len'
    exact ParseStrRoom.heap_room_mono hr (Nat.le_add_left tail pages)
  · subst len'
    rcases hr with ⟨ha, hp, hm, hw⟩
    refine ⟨by simp [Nat.add_mod, ha], Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _), ?_, ?_⟩
    · simpa only [Nat.add_mul, Nat.add_assoc] using hm
    · simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hw

/-- A model-accepted account uses at most five scratch-growth pages and one owned-value page. -/
theorem copied_parser_pages_le (bs : List UInt8) (a : WNear.AccountId) (q : Nat) (rest : List UInt8)
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some a.val, rest))
    (hlen : bs.length < 2 ^ 24) : copiedParserPages bs q a ≤ 6 := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hshort : a.val.toUTF8.toList.length ≤ 64 := by omega
  have hok := (SerdeAccountIdEsc.strRun_of_stringBody (bs.drop q) a.val rest hmodel).1
  have hsmall : ([] : List UInt8).length + (bs.drop q).length < 2 ^ 27 := by
    simp only [List.length_nil, Nat.zero_add, List.length_drop]; omega
  have hcount := ParseStrSuccess.appendChunks_growthCount 0 [] (bs.drop q) a.val.toUTF8.toList rest
    hok (by simp) (by decide) hsmall
  have hpages := ParseStrSuccess.appendChunks_pages 0 [] (bs.drop q) a.val.toUTF8.toList rest
    hok (by simp) (by decide) hsmall
  change ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) []) = 0 ∨
    8 * 2 ^ (ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) []) - 1) ≤
      2 * a.val.toUTF8.toList.length + 8 at hcount
  change growthPages 0 0 (appendChunks (bs.drop q) []) ≤
    (4 * a.val.toUTF8.toList.length + 16 +
      66066 * ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) [])) / 65536 at hpages
  have hcount5 : ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) []) ≤ 5 := by
    rcases hcount with hz | hp
    · omega
    · by_contra! hn
      have he : 2 ^ 5 ≤ 2 ^ (ScratchGrow.growthCount 0 0 (appendChunks (bs.drop q) []) - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega
  have hg : growthPages 0 0 (appendChunks (bs.drop q) []) ≤ 5 := by
    omega
  unfold copiedParserPages
  have hsize : (UInt32.ofNat a.val.toUTF8.toList.length).toNat ≤ 64 := by
    rw [UInt32.toNat_ofNat']
    exact (Nat.mod_le _ _).trans hshort
  have hc : (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat a.val.toUTF8.toList.length)) 1).toNat = 1 :=
    LookupMapOps.cellPages_le4096 _ (hsize.trans (by decide))
  rw [hc]
  omega

/-- The input allocation uses at most 257 pages below the existing 2^24-byte bound. -/
theorem input_pages_le (bs : List UInt8) (hlen : bs.length < 2 ^ 24) :
    (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat ≤ 257 := by
  have hsize : (UInt32.ofNat bs.length).toNat < 2 ^ 24 :=
    (Nat.mod_le _ _).trans_lt hlen
  have hw : (AllocAlloc.wordsOf (UInt32.ofNat bs.length)).toNat =
      ((UInt32.ofNat bs.length).toNat + 3) / 4 := by
    unfold AllocAlloc.wordsOf
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt (by omega))
  have hsw : (AllocAlloc.wordsOf (UInt32.ofNat bs.length)).toNat < 2 ^ 29 := by
    rw [hw]; omega
  rw [AllocNewCell.cellPages_toNat _ _ hsw (by decide),
    AllocNewCell.cellBytes_toNat _ _ hsw (by decide), hw]
  simp only [UInt32.reduceToNat]
  omega

/-- The actual instantiated 1024-page memory supplies the complete input-plus-parser allowance. -/
theorem initial_memory_room (bs : List UInt8) (hlen : bs.length < 2 ^ 24) :
    HeapRoomK ((AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat + 131)
      InitialState.memLen 2048 := by
  have hp := input_pages_le bs hlen
  have h388 : HeapRoomK 388 InitialState.memLen 2048 := by
    unfold HeapRoomK InitialState.memLen
    decide +kernel
  exact ParseStrRoom.heap_room_mono h388 (by omega)

/-- The same initial page bound supplies the old body budget and every parser-room instance.
The short decoded account bounds all scratch reserves, including error boxes. -/
theorem initial_parser_and_body_room (bs : List UInt8) (a : WNear.AccountId)
    (q len : Nat) (rest : List UInt8) (hlen : bs.length < 2 ^ 24)
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some a.val, rest))
    (hr : HeapRoomK ((AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
      131) len 2048) :
    HeapRoomK ((AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat bs.length)) 1).toNat +
      copiedParserPages bs q a + 6) len 2048 ∧
    ∀ len', len' = len ∨ len' = grownLen len (UInt32.ofNat bs.length) →
      roomRun 2048 len' 0 [] (bs.drop q) := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hshort : a.val.toUTF8.toList.length ≤ 64 := by omega
  have hpages := copied_parser_pages_le bs a q rest hmodel hlen
  refine ⟨ParseStrRoom.heap_room_mono hr (by omega), ?_⟩
  intro len' hstep
  have htail := room_after_input_pages hr hstep
  exact ParseStrRoom.roomRun_of_short_stringBody 2048 len' (bs.drop q) rest a.val hmodel hshort htail

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The complete copied-array absent-account body at the instantiated memory size, without room hypotheses. -/
theorem array_absent_body_initial_memory (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (a : WNear.AccountId) (live : List (Nat × Nat))
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

    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
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
    (hnone : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none)
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    codeA inst mi A ∗ inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
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
      heapInv n 2048 InitialState.memLen live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
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
    mwpi cfg lim d ⟨#[.i32 0, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩ [] f297.body Φ := by
  have hroom := initial_memory_room bs hlen
  obtain ⟨hroom', hparserRoom⟩ := initial_parser_and_body_room bs a (j + 1)
    InitialState.memLen jsonRest hlen hmodel hroom
  exact array_absent_body_initial_room cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    idx InitialState.memLen a live bs oldOpt optTail oldVec jsonRest derefOut j k ob stateTail contractTail destTail out head
    oldA oldB oldC oldD hookOld k3 hs hal hframe hopt hoptTail holdVec hderef hlen ho hj hq he hk hend hmodel
     hparserRoom hob hstateTail hcontractTail hdestTail hA hB hout hhead h0 h hinput hafter
    hinputLimit S st hv hroom' hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The existing copied-only contract, preserved as a checked specialization. -/
theorem copied_array_absent_body_initial_memory (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (a : WNear.AccountId) (live : List (Nat × Nat))
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
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
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
    (hnone : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none)
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    codeA inst mi A ∗ inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
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
      heapInv n 2048 InitialState.memLen live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
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
    mwpi cfg lim d ⟨#[.i32 0, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩ [] f297.body Φ := by
  exact array_absent_body_initial_memory cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3 idx a live bs oldOpt optTail oldVec jsonRest derefOut j k ob stateTail contractTail destTail out head oldA oldB oldC oldD hookOld k3 hs hal hframe hopt hoptTail holdVec hderef hlen ho hj hq he hk hend hmodel hob hstateTail hcontractTail hdestTail hA hB hout hhead h0 h hinput hafter hinputLimit S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ
end Spec
end WNear.Binary.BalanceOf297AbsentCall
