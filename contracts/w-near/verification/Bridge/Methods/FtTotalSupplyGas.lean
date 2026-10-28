import Bridge.Methods.FtTotalSupplyModel

/-!
# `ft_total_supply` (296): the model's gas bound covers the method

`hbound_wnear` discharges `hbound` of `ftTotalSupply_refines_wnear`: loading plus the method's
proved cost (`cost`: the entry activation and `cost296`) is at most the model's
`gasBound ctx .ftTotalSupply = computeGas + trieGas ctx + returnDataGas ctx 41`.

* `cost_le`: `cost` is at most `22000` regular ops, four linear-op charges (`memory.grow` of one
  page in each of the four allocations that grow the heap), the ext costs of `storage_read`,
  `register_len`, `read_register` and `value_return` (`extUse`), the trie nodes of the `STATE`
  read, the data receipts of the return value and the assumed `x96`. Every value-dependent
  part (the `u128` formatting, the digit count) is bounded over all `u128`s.
* `trie_le`: the `STATE` read's trie nodes (`2 · |contractKey| + 1` at the dearer node cost) are
  within `trieGas` (which pays `3 + 8` times as many nodes of the longest key, at both costs).
* `dataGas_le`: `value_return`'s data receipts for at most 41 bytes are within
  `returnDataGas ctx 41` (41 bytes: the JSON of `2^128 - 1`, `retBytes`).
* `hbound_wnear`: under `CostsV86` (the protocol-86 cost parameters, as upper bounds: the kernel
  cannot evaluate `RuntimeConfig.parse wNearProtocolJson`), a code size of at most 185625 bytes
  (`contract.wasm`'s) and `x96 ≤ 3·10^12`: the rest is below 0.3 Tgas against `computeGas = 4`
  Tgas.
* `ftTotalSupply_refines_v86`: `ftTotalSupply_refines_wnear` with `hag` and `hbound` discharged.
-/

namespace WNear.Binary.FtTotalSupplyMethod

open Wasm Wasm.Near WasmLogic NearLogic WNear.Binary

/-! ## Bounds on the value-dependent parts -/

theorem parse_le (v : Nat) : FmtParseU64.cost v ≤ 291 := by
  simp only [FmtParseU64.cost, FmtParseU64.cost4, FmtParseU64.cost2, FmtParseU64.cost1]
  split_ifs <;> omega
theorem memset_le (n : Nat) : MemSet.cost n ≤ 13 * n + 6 := by
  unfold MemSet.cost; split <;> omega
theorem memcpy_le (n : Nat) : MemCpy.cost n ≤ 18 * n + 6 := by
  unfold MemCpy.cost; split <;> omega
theorem fmt_le (lo hi : UInt64) : FmtU128.cost lo hi ≤ 1927 := by
  have a := parse_le ((FmtU128.val lo hi) % 10 ^ 19)
  have b := parse_le ((FmtU128.val lo hi) / 10 ^ 19 % 10 ^ 19)
  have c := memset_le (19 - (FmtDigits.decDigits (FmtU128.val lo hi % 10 ^ 19)).length)
  have d := memset_le (20 - (FmtDigits.decDigits (FmtU128.val lo hi / 10 ^ 19 % 10 ^ 19)).length - 1)
  simp only [FmtU128.cost, FmtU128.costR1, FmtU128.costRounds, FmtU128.costR3]
  split_ifs <;> omega
theorem act872 (c : Nat) : activationGas c (entryLocals f872 [.i32 0, .i32 0, .i32 0]) ≤ 40 * c := by
  unfold activationGas
  simp [entryLocals, f872, ValType.default]; try omega
theorem act759 (c : Nat) : activationGas c (entryLocals f759 [.i32 0, .i32 0, .i32 0]) ≤ 40 * c := by
  unfold activationGas
  simp [entryLocals, f759]; try omega
theorem act353 (c : Nat) : activationGas c (entryLocals f353 [.i32 0, .i32 0]) ≤ 40 * c := by
  unfold activationGas
  simp [entryLocals, f353]; try omega
theorem pages_newCap : ∀ k : Fin 40, (AllocNewCell.cellPages (AllocAlloc.wordsOf (FmtGrow.newCap 0 (UInt32.ofNat k))) 1).toNat ≤ 1 := by
  decide
theorem pages_fixed : (AllocNewCell.cellPages (AllocAlloc.wordsOf 29) 1).toNat ≤ 1 ∧
    (AllocNewCell.cellPages (AllocAlloc.wordsOf 1) 1).toNat ≤ 1 ∧ (AllocNewCell.cellPages (AllocAlloc.wordsOf 128) 1).toNat ≤ 1 := by
  decide
theorem retBytes : (WNear.Ret.u128 (WNear.u128Bound - 1)).json.utf8ByteSize = 41 := by
  decide
theorem and0 : ((0 : UInt32) &&& 255 = 0) := by decide

variable (cfg : WasmConfig)
local notation "c" => cfg.regularOpCost
local notation "L" => cfg.linearOpBaseCost + cfg.linearOpUnitCost

theorem c581 (s : UInt32) (hp : (AllocNewCell.cellPages (AllocAlloc.wordsOf s) 1).toNat ≤ 1) :
    AllocZeroed.cost581 cfg s 1 ≤ 910 * c + L := by
  unfold AllocZeroed.cost581
  have := Nat.mul_le_mul_left cfg.linearOpUnitCost hp
  omega

theorem cAllocF (s : UInt32) (hp : (AllocNewCell.cellPages (AllocAlloc.wordsOf s) 1).toNat ≤ 1) :
    VecFromElem.costAlloc cfg false s ≤ 940 * c + L := by
  have := c581 cfg s hp
  simp only [VecFromElem.costAlloc, Bool.false_eq_true, ite_false]
  omega

theorem c687 : VecFromElem.cost687 cfg 0 (UInt32.ofNat 29) ≤ 1600 * c + L := by
  have := c581 cfg (UInt32.ofNat 29) pages_fixed.1
  simp only [VecFromElem.cost687, and0, ite_true, VecFromElem.costAlloc, AllocZeroed.cost153,
    show MemSet.cost (UInt32.ofNat 29).toNat = 383 by rfl]
  omega

theorem c161 : BorshContract.cost161 cfg 1 ≤ 5572 * c + L := by
  have := cAllocF cfg 1 pages_fixed.2.1
  simp only [BorshContract.cost161, BorshFT.cost425, BorshVec.cost374, show MemCpy.cost (1 : UInt32).toNat = 24 by rfl]
  omega

theorem c353 (lo hi : UInt64) : FmtString.cost353 cfg lo hi ≤ 4105 * c + L := by
  have hk := FmtString.kOf_toNat lo hi
  have hd := FmtString.decDigits_le lo hi
  have hp := pages_newCap ⟨(FmtString.kOf (FmtU128.val lo hi)).toNat, by omega⟩
  simp only [UInt32.ofNat_toNat] at hp
  have h1 := cAllocF cfg _ hp
  have h2 := Nat.mul_le_mul_right c (fmt_le lo hi)
  have h3 := Nat.mul_le_mul_right c (memcpy_le (FmtString.kOf (FmtU128.val lo hi)).toNat)
  have h4 := act759 c
  simp only [FmtString.cost353, FmtString.costGrow]
  have h5 : (18 * (FmtString.kOf (FmtU128.val lo hi)).toNat + 6) * c ≤ 708 * c :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem c96 (lo hi : UInt64) : ToVec.cost96 cfg lo hi ≤ 9515 * c + 2 * L := by
  have hk := FmtString.kOf_toNat lo hi
  have hd := FmtString.decDigits_le lo hi
  have a := c353 cfg lo hi
  have b := cAllocF cfg 128 pages_fixed.2.2
  have h1 := act872 c
  have h2 := act759 c
  have h3 := act353 c
  have h4 : SerializeStr.cost383 (FmtString.kOf (FmtU128.val lo hi)).toNat * c ≤ 2648 * c := by
    apply Nat.mul_le_mul_right
    have := memcpy_le (FmtString.kOf (FmtU128.val lo hi)).toNat
    simp only [SerializeStr.cost383, SerializeStr.cost344, show MemCpy.cost 1 = 24 by rfl]
    omega
  simp only [ToVec.cost96, ToString.cost385, FmtString.cost746, FmtString.cost872,
    show MemCpy.cost 0 = 4 by rfl]
  omega

open WNear.Binary.FtTotalSupply WNear.Binary.FtTotalSupplyMethod in
/-- The ext costs of `ft_total_supply`'s host calls, the trie nodes and the data receipts aside. -/
def extUse (h : NearState) (n : Nat) : Nat :=
  let E := h.extCosts.cost
  -- storage_read of the 5-byte key, a 29-byte value into a register
  (E "base" + E "storage_read_base" + E "read_memory_base" + E "read_memory_byte" * 5 +
    E "storage_read_key_byte" * 5 + E "storage_read_value_byte" * 29 + E "write_register_base" +
    E "write_register_byte" * 29) +
  -- register_len
  E "base" +
  -- read_register of 29 bytes
  (E "base" + E "read_register_base" + E "read_register_byte" * 29 + E "write_memory_base" +
    E "write_memory_byte" * 29) +
  -- value_return of n bytes (its data receipts aside)
  (E "base" + E "read_memory_base" + E "read_memory_byte" * n)

open WNear.Binary.FtTotalSupply WNear.Binary.FtTotalSupplyMethod in
theorem cost_le (rc : RuntimeConfig) (h : NearState) (S : WNear.State) (x96 : Nat)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) :
    FtTotalSupplyMethod.cost rc S x96 h ≤ 22000 * rc.wasm.regularOpCost + 4 * (rc.wasm.linearOpBaseCost + rc.wasm.linearOpUnitCost) +
      extUse h (supplyJson S).length +
      (2 * (Near.TrieOverlay.contractKey h.context.currentAccountId StateRead.stateKey).length + 1) * trieNodeMax h +
      valueReturnDataGas h (supplyJson S).length + x96 := by
  have a := c96 rc.wasm (loOf S) (hiOf S)
  have b := c161 rc.wasm
  have d := c687 rc.wasm
  rw [← StateRead.stateKey_eq] at hv
  simp only [FtTotalSupplyMethod.cost, cost296, cost219, storageReadUse, StorageReadWrap.costS, ReadRegister.costRest,
    registerLenUse, readRegisterUse, valueReturnUse, hv, StateReadModel.header_length, storageReadPhaseUse,
    Option.map_some, Option.getD_some, chargesUse, storageReadBeforeCharges, storageReadValueCharges,
    writeReg, registerLenChargeList, readRegisterChargeList, valueReturnChargeList, List.map, List.sum_cons,
    List.sum_nil, chargeUse, extUse, List.cons_append, List.nil_append,
    show ¬ (29 > 4000) by decide, ite_false]
  omega

theorem bytes_inj {a b : NearInterface.AccountId} (h : a.bytes = b.bytes) : a = b := by
  apply Subtype.ext
  unfold NearInterface.AccountId.bytes at h
  rw [ToVec.toList_eq, ToVec.toList_eq, Array.toList_inj] at h
  apply String.toByteArray_inj.1
  rw [← String.toUTF8_eq_toByteArray, ← String.toUTF8_eq_toByteArray]
  exact ByteArray.ext h

open NearInterface in
theorem dataGas_le (ctx : Context) (raw : RawStorage) (n : Nat) (hn : n ≤ 41) :
    valueReturnDataGas (erase (hostOf ctx raw)) n ≤ returnDataGas ctx 41 := by
  have hr : (erase (hostOf ctx raw)).outputDataReceivers = ctx.outputDataReceivers.map NearInterface.AccountId.bytes := rfl
  have hc : (erase (hostOf ctx raw)).context.currentAccountId = ctx.current.bytes := rfl
  have hf : (erase (hostOf ctx raw)).fees = ctx.protocol.fees.actionFees := rfl
  unfold valueReturnDataGas returnDataGas
  rw [hr, hc, hf, List.map_map]
  generalize ctx.outputDataReceivers = l
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp]
    have hsir : (r.bytes == ctx.current.bytes) = decide (r = ctx.current) := by
      by_cases h : r = ctx.current
      · subst h; simp
      · simp only [h, decide_false]
        exact beq_eq_false_iff_ne.2 fun e => h (bytes_inj e)
    rw [hsir]
    have a := Nat.mul_le_mul_left (ctx.protocol.fees.actionFees.newDataReceiptByte.send (decide (r = ctx.current))) hn
    have b := Nat.mul_le_mul_left ctx.protocol.fees.actionFees.newDataReceiptByte.execution hn
    dsimp only at ih
    rw [Nat.add_mul]
    omega

theorem supplyJson_length (S : WNear.State) : (FtTotalSupply.supplyJson S).length ≤ 41 := by
  have : S.totalSupply % 2 ^ 128 < 10 ^ 39 := by
    have := Nat.mod_lt S.totalSupply (show 0 < 2 ^ 128 by norm_num); norm_num at this ⊢; omega
  have := FmtDigits.decDigits_length_le 39 _ (by norm_num) this
  simp only [FtTotalSupply.supplyJson, FtTotalSupply.jsonOf, List.length_append, List.length_cons, List.length_nil]
  omega

theorem trie_le (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) :
    (2 * (Near.TrieOverlay.contractKey (erase (hostOf ctx raw)).context.currentAccountId StateRead.stateKey).length + 1) *
      trieNodeMax (erase (hostOf ctx raw)) ≤ WNear.trieGas ctx := by
  have hc : (erase (hostOf ctx raw)).context.currentAccountId = ctx.current.bytes := rfl
  rw [hc]
  simp only [WNear.trieGas, WNear.trieNodes, WNear.storageKeysTouched, WNear.storageAccesses,
    WNear.maxStorageKeyBytes, WNear.maxAccountIdBytes, trieNodeMax, Near.TrieOverlay.contractKey,
    StateRead.stateKey, List.length_append, List.length_cons, List.length_nil]
  have hx : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  rw [hx]
  set t := ctx.protocol.wasm.extCosts.cost "touching_trie_node"
  set r := ctx.protocol.wasm.extCosts.cost "read_cached_trie_node"
  set len := ctx.current.bytes.length
  have hm : max t r ≤ t + r := max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have h1 := Nat.mul_le_mul (show 2 * (0 + 1 + len + (0 + 1) + (0 + 1 + 1 + 1 + 1 + 1)) + 1 ≤ 2 * (2 + len + (1 + 4 + 64)) + 1 by omega) hm
  nlinarith

/-- The protocol-86 values (`runtime_config_v86.json`, `wasm_config`) of the cost parameters
`ft_total_supply` pays, as upper bounds. -/
structure CostsV86 (p : RuntimeConfig) : Prop where
  regularOp : p.wasm.regularOpCost ≤ 822756
  linearBase : p.wasm.linearOpBaseCost ≤ 26328192
  linearUnit : p.wasm.linearOpUnitCost ≤ 822756
  base : p.wasm.extCosts.cost "base" ≤ 264768111
  loadingBase : p.wasm.extCosts.cost "contract_loading_base" ≤ 35445963
  loadingBytes : p.wasm.extCosts.cost "contract_loading_bytes" ≤ 1089295
  readMemoryBase : p.wasm.extCosts.cost "read_memory_base" ≤ 2609863200
  readMemoryByte : p.wasm.extCosts.cost "read_memory_byte" ≤ 3801333
  writeMemoryBase : p.wasm.extCosts.cost "write_memory_base" ≤ 2803794861
  writeMemoryByte : p.wasm.extCosts.cost "write_memory_byte" ≤ 2723772
  readRegisterBase : p.wasm.extCosts.cost "read_register_base" ≤ 2517165186
  readRegisterByte : p.wasm.extCosts.cost "read_register_byte" ≤ 98562
  writeRegisterBase : p.wasm.extCosts.cost "write_register_base" ≤ 2865522486
  writeRegisterByte : p.wasm.extCosts.cost "write_register_byte" ≤ 3801564
  storageReadBase : p.wasm.extCosts.cost "storage_read_base" ≤ 56356845749
  storageReadKeyByte : p.wasm.extCosts.cost "storage_read_key_byte" ≤ 30952533
  storageReadValueByte : p.wasm.extCosts.cost "storage_read_value_byte" ≤ 5611004

open NearInterface FtTotalSupply FtTotalSupplyMethod in
theorem hbound_wnear (cfg : WNear.Config) (ctx : Context) (raw : RawStorage) (st : Option WNear.State)
    (S : WNear.State) (x96 size : Nat) (hpre : pre S (erase (hostOf ctx raw))) (hc : CostsV86 ctx.protocol)
    (hsize : size ≤ 185625) (hx : x96 ≤ 3 * 10 ^ 12) :
    chargesUse (hostOf ctx raw) (loadingCharges size) + FtTotalSupplyMethod.cost ctx.protocol S x96 (erase (hostOf ctx raw)) ≤
      (WNear.wnear cfg).gas ctx st .ftTotalSupply := by
  obtain ⟨rs, hr⟩ := hpre
  have hcost := cost_le ctx.protocol (erase (hostOf ctx raw)) S x96 hr.value
  have htrie := trie_le ctx raw
  have hn := supplyJson_length S
  have hdata := dataGas_le ctx raw _ hn
  have hgas : (WNear.wnear cfg).gas ctx st .ftTotalSupply =
      WNear.computeGas + WNear.trieGas ctx + returnDataGas ctx 41 := by
    show WNear.gasBound ctx .ftTotalSupply = _
    simp only [WNear.gasBound, WNear.Call.attachedGas, WNear.Call.receiptGas, WNear.Call.readsArguments,
      WNear.Call.resultBytes, WNear.Call.returnBytes, retBytes]
    simp
  have hx' : (erase (hostOf ctx raw)).extCosts = ctx.protocol.wasm.extCosts := rfl
  have hl : chargesUse (hostOf ctx raw) (loadingCharges size) =
      ctx.protocol.wasm.extCosts.cost "contract_loading_bytes" * size +
        ctx.protocol.wasm.extCosts.cost "contract_loading_base" * 1 := by
    simp [chargesUse, loadingCharges, chargeUse]; rfl
  have hlb := Nat.mul_le_mul hc.loadingBytes hsize
  have hrm := Nat.mul_le_mul hc.readMemoryByte hn
  simp only [extUse, hx'] at hcost
  rw [hgas, hl]
  simp only [WNear.computeGas]
  have := hc.regularOp; have := hc.linearBase; have := hc.linearUnit; have := hc.base
  have := hc.loadingBase; have := hc.readMemoryBase; have := hc.readMemoryByte; have := hc.writeMemoryBase
  have := hc.writeMemoryByte; have := hc.readRegisterBase; have := hc.readRegisterByte
  have := hc.writeRegisterBase; have := hc.writeRegisterByte; have := hc.storageReadBase
  have := hc.storageReadKeyByte; have := hc.storageReadValueByte
  omega

open NearInterface ContractModel in
/-- **`ft_total_supply` refines the model** (the clauses of `Refines` for a call to it), with the
model's side discharged: `hag` from `Represents` (`hag_wnear`), `hbound` from the protocol-86 cost
parameters (`hbound_wnear`). Left: `H96` (`to_vec` on a two-cell free list, and its extra cost
`x96 ≤ 3·10^12`), `hpre` (the host reads `S`: the storage premises of `storage_read`), the code
size, and `CostsV86`. -/
theorem ftTotalSupply_refines_v86 (cfg : WNear.Config) (size : Nat) (codeOf : List UInt8 → Near.ContractCode)
    (raw : RawStorage) (st : Option WNear.State) (ctx : Context) (S : WNear.State) (x96 : Nat)
    (H96 : FtTotalSupply.ToVecAfterFree ctx.protocol.wasm execLimits x96) (hp : WProtocol ctx.protocol)
    (hwf : ctx.WF raw) (hrep : (WNear.wnear cfg).Represents raw st)
    (hm : ctx.method = "ft_total_supply") (hpre : pre S (erase (hostOf ctx raw)))
    (hc : CostsV86 ctx.protocol) (hsize : size ≤ 185625) (hx : x96 ≤ 3 * 10 ^ 12) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx st .ftTotalSupply
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx st .ftTotalSupply ≤ ctx.gasLimit →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx st .ftTotalSupply) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (r.outcome = .error .outOfGas ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) :=
  ftTotalSupply_refines_wnear cfg size codeOf raw st ctx S x96 H96 hp hwf hm hpre
    (hag_wnear cfg ctx raw st S hrep hwf hpre) (hbound_wnear cfg ctx raw st S x96 size hpre hc hsize hx)

end WNear.Binary.FtTotalSupplyMethod
