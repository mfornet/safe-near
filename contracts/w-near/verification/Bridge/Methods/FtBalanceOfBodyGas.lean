import Bridge.Methods.FtBalanceOfParserGas

/-! The initialized copied-array absent-body gas, with explicit host charges. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic WNear.Binary
open SerdeRead ParseStrSuccess ParseStr ParseEscape NearInterface.Json

theorem alloc32_delta (cfg : WasmConfig) (F : Nat) (size : UInt32) (hF : F ≤ 32) :
    VecWithCap.costAllocF cfg F size ≤ VecFromElem.costAlloc cfg false size + 10270 * cfg.regularOpCost := by
  unfold VecWithCap.costAllocF
  split
  · omega
  · have hf := Nat.mul_le_mul_right (320 * cfg.regularOpCost) hF
    simp only [AllocWalk.cost310W, AllocWalk.walkCost, AllocWalk.wc,
      VecFromElem.costAlloc, Bool.false_eq_true, ite_false, AllocZeroed.cost581]
    omega

theorem allocW32_delta (cfg : WasmConfig) (F : Nat) (size : UInt32) (hF : F ≤ 32) :
    AllocZeroedF.costAllocW cfg F size ≤ VecFromElem.costAlloc cfg false size + 10270 * cfg.regularOpCost := by
  unfold AllocZeroedF.costAllocW
  split
  · omega
  · have hf := Nat.mul_le_mul_right (320 * cfg.regularOpCost) hF
    simp only [AllocWalk.cost310W, AllocWalk.walkCost, AllocWalk.wc,
      VecFromElem.costAlloc, Bool.false_eq_true, ite_false, AllocZeroed.cost581]
    omega

theorem vec_zero32_delta (cfg : WasmConfig) (F : Nat) (size : UInt32) (hF : F ≤ 32) :
    VecFromElemF.cost687Z cfg F size ≤ VecFromElem.cost687 cfg 0 size + 10270 * cfg.regularOpCost := by
  have ha := allocW32_delta cfg F size hF
  rw [VecFromElemF.cost687Z, AllocZeroedF.costZeroF_eq]
  simp only [VecFromElem.cost687, FtTotalSupplyMethod.and0, ite_true, VecFromElem.costAlloc,
    ite_true, Bool.false_eq_true, ite_false, AllocZeroed.cost153] at ha ⊢
  omega

theorem return32_cost_le (cfg : WasmConfig) (F : Nat) (lo hi : UInt64) (hF : F ≤ 32) :
    ToVec.cost96F cfg F lo hi ≤ 31000 * cfg.regularOpCost + 2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) := by
  have ho := FtTotalSupplyMethod.c96 cfg lo hi
  have h1 := alloc32_delta cfg F 128 hF
  have h2 := alloc32_delta cfg F (FmtGrow.newCap 0 (FmtString.kOf (FmtU128.val lo hi))) hF
  simp only [ToVec.cost96, ToVec.cost96F, ToString.cost385, FmtString.cost746, FmtString.cost872,
    FmtString.cost353, FmtString.costGrow,
    VecWithCap.costAllocF_le2 cfg (show 1 ≤ 2 by decide)] at ho ⊢
  omega

theorem read_register32_delta (cfg : WasmConfig) (F : Nat) (h : NearState) (r : UInt64) (hF : F ≤ 32) :
    ReadRegisterF.cost523F cfg F h r ≤ ReadRegister.cost523 cfg h r + 10270 * cfg.regularOpCost := by
  cases hr : h.registers r.toNat with
  | none => simp only [ReadRegisterF.cost523F, ReadRegister.cost523, hr, ReadRegisterF.costRestF, ReadRegister.costRest]; omega
  | some val =>
    have hz := vec_zero32_delta cfg F (UInt32.ofNat val.length) hF
    simp only [ReadRegisterF.cost523F, ReadRegister.cost523, hr, ReadRegisterF.costRestF, ReadRegister.costRest]
    omega

theorem storage_register32_delta (cfg : WasmConfig) (F : Nat) (h : NearState) (v : List UInt8) (hF : F ≤ 32) :
    StorageReadWrapF.costSF cfg F h v ≤ StorageReadWrap.costS cfg h (some v) + 10270 * cfg.regularOpCost := by
  have hr := read_register32_delta cfg F (h.setRegister 0 v) 0 hF
  have he : ReadRegister.cost523 cfg (h.setRegister 0 v) 0 =
      281 * cfg.regularOpCost + NearLogic.registerLenUse h + ReadRegister.costRest cfg h (some v) := rfl
  rw [he] at hr
  simp only [StorageReadWrapF.costSF, StorageReadWrap.costS]
  omega

theorem borsh_contract32_delta (cfg : WasmConfig) (F : Nat) (L : UInt32) (hF : F ≤ 32) :
    BorshContractF.cost161 cfg F L ≤ BorshContract.cost161 cfg L + 10270 * cfg.regularOpCost := by
  have ha := alloc32_delta cfg F L hF
  simp only [BorshContractF.cost161, BorshContract.cost161, BorshFTF.cost425, BorshFT.cost425,
    BorshVecF.cost374, BorshVec.cost374]
  omega

theorem state_read32_delta (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State) (hF : F ≤ 32) :
    cost219F cfg F h S ≤ FtTotalSupply.cost219 cfg h S + 20540 * cfg.regularOpCost := by
  have hs := storage_register32_delta cfg F h (WNear.header S) hF
  have hb := borsh_contract32_delta cfg F 1 hF
  simp only [cost219F, FtTotalSupply.cost219]
  omega

theorem state_read32_cost_le (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State) (hF : F ≤ 32) :
    cost219F cfg F h S ≤ 31000 * cfg.regularOpCost +
      2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) + NearLogic.storageReadUse h StateRead.stateKey 5 +
      NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 := by
  have hf := state_read32_delta cfg F h S hF
  have hb := FtTotalSupplyMethod.c161 cfg
  have hv := FtTotalSupplyMethod.c687 cfg
  simp only [FtTotalSupply.cost219, StorageReadWrap.costS, ReadRegister.costRest, StateReadModel.header_length] at hf
  omega

theorem lookup_none32_cost_le (cfg : WasmConfig) (F : Nat) (L : UInt32) (h : NearState) (key : List UInt8)
    (hF : F ≤ 32) (hL : L.toNat ≤ 64) :
    LookupMapGet.cost399None cfg F 1 L h key ≤
      30000 * cfg.regularOpCost + 2 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
      NearLogic.storageReadUse h key (5 + L.toNat) := by
  have h4 : (0 + 4 + L : UInt32).toNat = 4 + L.toNat := by
    simp only [UInt32.toNat_add, UInt32.reduceToNat]
    omega
  have h5 : (1 + (0 + 4 + L) : UInt32).toNat = 5 + L.toNat := by
    simp only [UInt32.toNat_add, h4, UInt32.reduceToNat]
    omega
  have hp := LookupMapOps.cellPages_le4096 (1 + (0 + 4 + L)) (by rw [h5]; omega)
  have ha := alloc32_cost_le cfg F 1 1024 hF (by decide)
  have hb := alloc32_cost_le cfg F 1 (1 + (0 + 4 + L)) hF (by omega)
  have hc4 : MemCpy.cost 4 ≤ 78 := FtTotalSupplyMethod.memcpy_le 4
  have hcL : MemCpy.cost L.toNat ≤ 1158 := by have := FtTotalSupplyMethod.memcpy_le L.toNat; omega
  have hc1 : MemCpy.cost 1 ≤ 24 := by decide
  have hc4L : MemCpy.cost (0 + 4 + L : UInt32).toNat ≤ 1230 := by
    rw [h4]
    have := FtTotalSupplyMethod.memcpy_le (4 + L.toNat)
    omega
  have h4c := Nat.mul_le_mul_right cfg.regularOpCost hc4
  have hLc := Nat.mul_le_mul_right cfg.regularOpCost hcL
  have h1c := Nat.mul_le_mul_right cfg.regularOpCost hc1
  have h4Lc := Nat.mul_le_mul_right cfg.regularOpCost hc4L
  simp only [LookupMapGet.cost399None, LookupMapBorsh.cost395, LookupMapBorsh.cost377,
    LookupMapLeaves.cost510, h5, UInt32.reduceToNat, Nat.add_mul]
  omega

theorem input_cost_le (cfg : WasmConfig) (h : NearState) (bs : List UInt8)
    (hinput : h.context.input = bs) (hlen : bs.length < 2 ^ 24) :
    EnvInput.cost527 cfg h ≤ (2100 + 13 * bs.length) * cfg.regularOpCost + cfg.linearOpBaseCost +
      257 * cfg.linearOpUnitCost + NearLogic.inputUse h + NearLogic.registerLenUse (NearLogic.inputHost h 0) +
      NearLogic.readRegisterUse (NearLogic.inputHost h 0) bs.length := by
  have hr : (NearLogic.inputHost h 0).registers 0 = some bs := by
    simp [NearLogic.inputHost, show (0 : UInt64) ≠ u64Max by decide, NearState.setRegister, hinput]
  have hsize : (UInt32.ofNat bs.length).toNat = bs.length := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hp := input_pages_le bs hlen
  have hpg := Nat.mul_le_mul_left cfg.linearOpUnitCost hp
  have hms := Nat.mul_le_mul_right cfg.regularOpCost (FtTotalSupplyMethod.memset_le bs.length)
  simp only [Nat.add_mul] at hms
  simp only [EnvInput.cost527, ReadRegister.cost523, UInt64.reduceToNat, hr, ReadRegister.costRest,
    VecFromElem.cost687, FtTotalSupplyMethod.and0, ite_true, VecFromElem.costAlloc,
    AllocZeroed.cost153, AllocZeroed.cost581, hsize, Nat.add_mul]
  omega

theorem suffix_cost_le (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State) (a : WNear.AccountId)
    (hF : F ≤ 12) : parserSuccessCost cfg F h S a 0 ≤
      97000 * cfg.regularOpCost + 6 * (cfg.linearOpBaseCost + cfg.linearOpUnitCost) +
      NearLogic.storageReadUse h StateRead.stateKey 5 + NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 +
      NearLogic.storageReadUse h (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (5 + a.val.utf8ByteSize) +
      NearLogic.valueReturnUse h 3 := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hn : a.val.utf8ByteSize ≤ 64 := by
    rw [← Wasm.ByteEncoding.string_utf8_length]; exact hvalid.1.2
  have hsize : (UInt32.ofNat a.val.utf8ByteSize).toNat = a.val.utf8ByteSize := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hs := state_read32_cost_le cfg (F + 1) h S (by omega)
  have hl := lookup_none32_cost_le cfg (F + 2) (UInt32.ofNat a.val.utf8ByteSize) h
    (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (by omega) (by omega)
  have hr := return32_cost_le cfg (F + 5) 0 0 (by omega)
  rw [hsize] at hl
  simp only [parserSuccessCost, Nat.add_zero, Nat.add_assoc, Nat.reduceAdd]
  omega

/-- The exact gas expression consumed by the initialized copied-array absent body, with no continuation reserve. -/
noncomputable def initialBodyCost (cfg : WasmConfig) (h0 h : NearState) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (j k : Nat) : Nat :=
  475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + EnvInput.cost527 cfg h0 +
    (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
      (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
        SerdeStruct78Esc.costArray cfg 1 0 bs a.val.toUTF8.toList rest j)) +
      parserSuccessCost cfg (copiedParserFree bs (j + 1) 1) h S a 0)))))

/-- All host charges appearing in the exact copied-array absent-body bound. -/
def initialBodyHostUse (h0 h : NearState) (a : WNear.AccountId) (bs : List UInt8) : Nat :=
  NearLogic.inputUse h0 + NearLogic.registerLenUse (NearLogic.inputHost h0 0) +
    NearLogic.readRegisterUse (NearLogic.inputHost h0 0) bs.length +
    NearLogic.storageReadUse h StateRead.stateKey 5 + NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 +
    NearLogic.storageReadUse h (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (5 + a.val.utf8ByteSize) +
    NearLogic.valueReturnUse h 3

set_option maxRecDepth 20000 in
theorem initial_body_cost_le (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h0 h : NearState) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (j k : Nat)
    (hinput : h0.context.input = bs) (hlen : bs.length < 2 ^ 24)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (hk : k = bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest)) :
    initialBodyCost p.wasm h0 h S a bs rest j k ≤
      400 * 10 ^ 9 + (100 * 10 ^ 6) * bs.length + initialBodyHostUse h0 h a bs := by
  have hp := copied_array_parser_cost_le300b p hc bs a rest j k hlen hj hq hk hend hmodel
  have hi := input_cost_le p.wasm h0 bs hinput hlen
  have hF := copied_parser_free_le12 bs a (j + 1) rest hmodel hlen
  have hs := suffix_cost_le p.wasm (copiedParserFree bs (j + 1) 1) h S a hF
  have hcst := Nat.mul_le_mul_left 100923 hc.regularOp
  have hbase := Nat.mul_le_mul_left 7 hc.linearBase
  have hunit := Nat.mul_le_mul_left 263 hc.linearUnit
  have hlin : 13 * p.wasm.regularOpCost ≤ 20 * 10 ^ 6 := by have := hc.regularOp; omega
  have hlinear := Nat.mul_le_mul_right bs.length hlin
  simp only [initialBodyCost, initialBodyHostUse]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hp hi hlinear ⊢
  omega

theorem initial_host_input_eq (h : NearState) (a : WNear.AccountId) (bs : List UInt8) :
    initialBodyHostUse h (NearLogic.inputHost h 0) a bs =
    NearLogic.inputUse h + NearLogic.registerLenUse h + NearLogic.readRegisterUse h bs.length +
    NearLogic.storageReadUse h StateRead.stateKey 5 + NearLogic.registerLenUse h + NearLogic.readRegisterUse h 29 +
    NearLogic.storageReadUse h (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (5 + a.val.utf8ByteSize) +
    NearLogic.valueReturnUse h 3 := rfl

set_option maxRecDepth 20000 in
theorem initial_host_cost_le (p : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 p)
    (h : NearState) (S : WNear.State) (a : WNear.AccountId) (bs : List UInt8)
    (hext : h.extCosts = p.wasm.extCosts) (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hnone : h.storage (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none) :
    initialBodyHostUse h (NearLogic.inputHost h 0) a bs ≤
      200 * 10 ^ 9 + (10 * 10 ^ 6) * bs.length +
      NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey) * NearLogic.trieNodeMax h +
      NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) * NearLogic.trieNodeMax h +
      NearLogic.valueReturnDataGas h 3 := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hn : a.val.utf8ByteSize ≤ 64 := by
    rw [← Wasm.ByteEncoding.string_utf8_length]; exact hvalid.1.2
  have hk : 5 + a.val.utf8ByteSize ≤ 69 := by omega
  have hkm := Nat.mul_le_mul hc.readMemoryByte hk
  have hks := Nat.mul_le_mul hc.storageReadKeyByte hk
  have hcoef : p.wasm.extCosts.cost "read_register_byte" + p.wasm.extCosts.cost "write_memory_byte" ≤ 10 * 10 ^ 6 := by
    have := hc.readRegisterByte; have := hc.writeMemoryByte; omega
  have hlin := Nat.mul_le_mul_right bs.length hcoef
  have hv' : h.storage StateRead.stateKey = some (WNear.header S) := by simpa only [StateRead.stateKey_eq] using hv
  rw [initial_host_input_eq]
  simp only [NearLogic.inputUse, NearLogic.inputChargeList, NearLogic.registerLenUse, NearLogic.registerLenChargeList,
    NearLogic.readRegisterUse, NearLogic.readRegisterChargeList, NearLogic.storageReadUse, hv', hnone,
    NearLogic.storageReadPhaseUse, StateReadModel.header_length, Option.map_some, Option.getD_some,
    Option.map_none, Option.getD_none, NearLogic.chargesUse, NearLogic.chargeUse,
    NearLogic.storageReadBeforeCharges, storageReadValueCharges, writeReg, NearLogic.valueReturnUse, NearLogic.valueReturnChargeList,
    List.map, List.sum_cons, List.sum_nil, List.cons_append, List.nil_append,
    show ¬ (29 > 4000) by decide, ite_false, Nat.mul_one, Nat.add_zero, hext]
  have := hc.base; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte; have := hc.storageReadBase
  have := hc.storageReadKeyByte; have := hc.storageReadValueByte
  simp only [Nat.mul_add, Nat.add_mul] at hlin
  omega

theorem two_read_nodes_le (h : NearState) (key : List UInt8) (hk : key.length ≤ 69) :
    NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey) * NearLogic.trieNodeMax h +
    NearLogic.readNodes h (Near.TrieOverlay.contractKey h.context.currentAccountId key) * NearLogic.trieNodeMax h ≤
      3 * (2 * (2 + h.context.currentAccountId.length + 69) + 1) * h.extCosts.cost "touching_trie_node" +
      8 * (2 * (2 + h.context.currentAccountId.length + 69) + 1) * h.extCosts.cost "read_cached_trie_node" := by
  have hs := NearLogic.readNodes_mul_le h (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey)
  have ha := NearLogic.readNodes_mul_le h (Near.TrieOverlay.contractKey h.context.currentAccountId key)
  have hls : 2 * (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey).length + 1 ≤
      2 * (2 + h.context.currentAccountId.length + 69) + 1 := by
    simp only [Near.TrieOverlay.contractKey, StateRead.stateKey, List.length_append, List.length_cons, List.length_nil]
    omega
  have hla : 2 * (Near.TrieOverlay.contractKey h.context.currentAccountId key).length + 1 ≤
      2 * (2 + h.context.currentAccountId.length + 69) + 1 := by
    simp only [Near.TrieOverlay.contractKey, List.length_append, List.length_cons, List.length_nil]
    omega
  have hm : NearLogic.trieNodeMax h ≤ h.extCosts.cost "touching_trie_node" + h.extCosts.cost "read_cached_trie_node" :=
    max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hs' := hs.trans (Nat.mul_le_mul hls hm)
  have ha' := ha.trans (Nat.mul_le_mul hla hm)
  nlinarith

theorem initial_body_trie_le (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (a : WNear.AccountId) :
    NearLogic.readNodes (NearLogic.erase (hostOf ctx raw))
      (Near.TrieOverlay.contractKey (NearLogic.erase (hostOf ctx raw)).context.currentAccountId StateRead.stateKey) *
      NearLogic.trieNodeMax (NearLogic.erase (hostOf ctx raw)) +
    NearLogic.readNodes (NearLogic.erase (hostOf ctx raw))
      (Near.TrieOverlay.contractKey (NearLogic.erase (hostOf ctx raw)).context.currentAccountId
        (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) *
      NearLogic.trieNodeMax (NearLogic.erase (hostOf ctx raw)) ≤ WNear.trieGas ctx := by
  have hvalid := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hvalid
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hvalid
  have hkey : (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length ≤ 69 := by
    have hp : WNear.accountsPrefix.length = 1 := by decide +kernel
    have hw : (bytes32 (UInt32.ofNat a.val.utf8ByteSize)).length = 4 := by simp [bytes32]
    simp only [List.length_append, hp, hw]
    omega
  have hp := two_read_nodes_le (NearLogic.erase (hostOf ctx raw)) _ hkey
  have hcur : (NearLogic.erase (hostOf ctx raw)).context.currentAccountId = ctx.current.bytes := rfl
  have hext : (NearLogic.erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  simpa only [hcur, hext, WNear.trieGas, WNear.trieNodes, WNear.storageKeysTouched,
    WNear.storageAccesses, WNear.maxStorageKeyBytes, WNear.maxAccountIdBytes] using hp
end WNear.Binary.BalanceOf297AbsentCall
