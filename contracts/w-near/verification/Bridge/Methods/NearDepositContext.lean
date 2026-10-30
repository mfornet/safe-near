import Bridge.Methods.NearDepositStorage
import Bridge.Functions.Utf8
import NearLogic.Hosts.LogUtf8

/-!
# Context facts needed by initialized `near_deposit`

Typed context account IDs supply the length, UTF-8 and host-validation premises of
`PredecessorId.f526_spec`. Erasing gas and proof recording preserves these facts.
-/

namespace WNear.Binary.NearDepositMethod

open Wasm Wasm.Near NearLogic NearInterface

private theorem accountIdFormat_ascii (previous : Bool) (bs : List UInt8)
    (hf : accountIdFormat previous bs = true) : ∀ b ∈ bs, b.toNat < 128 := by
  induction bs generalizing previous with
  | nil => simp
  | cons b bs ih =>
    simp only [accountIdFormat] at hf
    split at hf
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · exact ih _ hf x hx
    · split at hf
      · rename_i hc
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact ih _ hf x hx
      · cases hf

/-- Every byte of a typed account ID is ASCII, as required for the deposit log. -/
theorem account_bytes_ascii (a : NearInterface.AccountId) : ∀ b ∈ a.bytes, b.toNat < 128 := by
  have ha := a.property
  change validAccountIdBytes a.bytes = true at ha
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact accountIdFormat_ascii _ _ ha.2

/-- Erasing resources preserves the ASCII predecessor bytes. -/
theorem predecessor_ascii_of_eraseP (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) : ∀ b ∈ h.context.predecessorAccountId, b.toNat < 128 := by
  have hp : h.context.predecessorAccountId = ctx.predecessor.bytes :=
    eraseP_field he (fun x => x.context.predecessorAccountId) fun _ => rfl
  rw [hp]
  exact account_bytes_ascii _

/-- Context account IDs are nonempty, at most 64 bytes, and valid UTF-8. -/
theorem account_bytes_properties (a : NearInterface.AccountId) :
    2 ≤ a.bytes.length ∧ a.bytes.length ≤ 64 ∧ Utf8.utf8Ok a.bytes = true := by
  have ha := a.property
  change validAccountIdBytes a.bytes = true at ha
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at ha
  refine ⟨ha.1.1, ha.1.2, Utf8.utf8Ok_of_ascii _ (accountIdFormat_ascii _ _ ha.2)⟩

/-- The predecessor retains its typed account bounds and UTF-8 validity under erasure. -/
theorem predecessor_properties_of_eraseP (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) :
    2 ≤ h.context.predecessorAccountId.length ∧ h.context.predecessorAccountId.length ≤ 64 ∧
      Utf8.utf8Ok h.context.predecessorAccountId = true := by
  have hp : h.context.predecessorAccountId = ctx.predecessor.bytes :=
    eraseP_field he (fun x => x.context.predecessorAccountId) fun _ => rfl
  rw [hp]
  exact account_bytes_properties ctx.predecessor

/-- The host accepts the typed predecessor under either account-validity rules version. -/
theorem predecessor_valid_of_eraseP (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) :
    h.config.validAccountId h.context.predecessorAccountId = true := by
  have hp : h.context.predecessorAccountId = ctx.predecessor.bytes :=
    eraseP_field he (fun x => x.context.predecessorAccountId) fun _ => rfl
  have hc : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  rw [hp, hc]
  change (if ctx.protocol.wasm.limits.accountIdValidityRulesVersion == 2 then validAccountIdBytes
    else fun _ => true) ctx.predecessor.bytes = true
  split
  · exact ctx.predecessor.property
  · rfl

/-- Protocol 86's existing register limit accommodates the predecessor account bytes. -/
theorem predecessor_register_fits (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol) :
    withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true := by
  have hc : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hp := predecessor_properties_of_eraseP ctx raw h he
  have hreg := hl.register
  rw [hc]
  change withinLimit (some ctx.protocol.wasm.limits.maxRegisterSize) _ = true
  simpa only [withinLimit, decide_eq_true_eq] using
    (show h.context.predecessorAccountId.length ≤ ctx.protocol.wasm.limits.maxRegisterSize by omega)

/-- The account-map key is at most 69 bytes and fits the protocol's storage-key limit. -/
theorem predecessor_key_fits (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol) :
    withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++
      (WasmLogic.bytes32 (UInt32.ofNat h.context.predecessorAccountId.length) ++ h.context.predecessorAccountId)).length =
      true := by
  have hc : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hp := predecessor_properties_of_eraseP ctx raw h he
  have hkey := hl.storageKey
  rw [hc]
  change withinLimit (some ctx.protocol.wasm.limits.maxLengthStorageKey) _ = true
  simp only [withinLimit, decide_eq_true_eq, List.length_append, StateReadModel.accountsPrefix_length,
    WasmLogic.bytes32, List.length_map, List.length_range]
  omega

/-- The initial host has room to emit a log when the protocol allows at least one. -/
theorem initial_log_room (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (hn : 1 ≤ ctx.protocol.wasm.limits.maxNumberLogs) :
    LogRoom h := by
  have hc : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hs : h.logs = [] := eraseP_field he NearState.logs fun _ => rfl
  intro limit hlimit
  rw [hc] at hlimit
  change some ctx.protocol.wasm.limits.maxNumberLogs = some limit at hlimit
  have hl := Option.some.inj hlimit
  simp only [hs, List.length_nil]
  omega

/-- Any message within the existing protocol-86 log bound fits the initially empty logs. -/
theorem initial_log_fits (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (n : Nat) (hn : n ≤ 16384) : LogFits h n := by
  have hc : h.config = (hostOf ctx raw).config := eraseP_field he NearState.config fun _ => rfl
  have hs : h.logs = [] := eraseP_field he NearState.logs fun _ => rfl
  have hb := hl.totalLog
  intro limit hlimit
  rw [hc] at hlimit
  change some ctx.protocol.wasm.limits.maxTotalLogLength = some limit at hlimit
  have hl := Option.some.inj hlimit
  simp only [hs, List.map_nil, List.sum_nil, Nat.zero_add]
  omega

/-- Reading any such message cannot overflow the host's `u64` byte charge. -/
theorem log_read_cost_fits (ctx : Context) (raw : RawStorage) (h : NearState)
    (he : eraseP h = eraseP (hostOf ctx raw)) (hc : FtTotalSupplyMethod.CostsV86 ctx.protocol)
    (n : Nat) (hn : n ≤ 16384) : h.extCosts.cost "read_memory_byte" * n < 2 ^ 64 := by
  have hx : h.extCosts = ctx.protocol.wasm.extCosts := eraseP_field he NearState.extCosts fun _ => rfl
  rw [hx]
  have hb := Nat.mul_le_mul hc.readMemoryByte hn
  omega

end WNear.Binary.NearDepositMethod
