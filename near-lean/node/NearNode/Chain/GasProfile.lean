import NearNode.Primitives.Outcome
import NearNode.Primitives.Account
import NearRuntime.Types

/-!
# The metadata of an outcome: gas profile and contracts

`ExecutionMetadata::V4` of a receipt's outcome (`runtime/runtime/src/lib.rs`, `apply_action_receipt`): the sum of the
profiles of its VM calls (`ProfileDataV3`: gas per `ActionCosts` entry, per `ExtCosts` entry and for Wasm instructions)
and the contract of the receiver before each action. A transaction's outcome has `ExecutionMetadata::V1`.

`ProfileDataV3` is stored as two arrays indexed by the discriminants of `ActionCosts` and `ExtCosts`
(`near-parameters/src/cost.rs`); the lists below are those enums in order, so a name's position is its index. The runtime
(`Near.GasProfileSplit`) names costs the way the VM does, by the `snake_case` names of the enum variants.
-/

namespace Near.Node.Chain

open Near.Node Near.Node.Borsh

/-- `ActionCosts` in discriminant order. -/
def actionCostNames : Array String :=
  #["create_account", "delete_account", "deploy_contract_base", "deploy_contract_byte",
    "function_call_base", "function_call_byte", "transfer", "stake", "add_full_access_key",
    "add_function_call_key_base", "add_function_call_key_byte", "delete_key", "new_action_receipt",
    "new_data_receipt_base", "new_data_receipt_byte", "delegate", "deploy_global_contract_base",
    "deploy_global_contract_byte", "use_global_contract_base", "use_global_contract_byte",
    "deterministic_state_init_base", "deterministic_state_init_byte",
    "deterministic_state_init_entry", "gas_key_transfer_base", "gas_key_byte",
    "gas_key_nonce_write_base"]

/-- `ExtCosts` in discriminant order. -/
def extCostNames : Array String :=
  #["base", "contract_loading_base", "contract_loading_bytes", "read_memory_base",
    "read_memory_byte", "write_memory_base", "write_memory_byte", "read_register_base",
    "read_register_byte", "write_register_base", "write_register_byte", "utf8_decoding_base",
    "utf8_decoding_byte", "utf16_decoding_base", "utf16_decoding_byte", "sha256_base",
    "sha256_byte", "keccak256_base", "keccak256_byte", "keccak512_base", "keccak512_byte",
    "ripemd160_base", "ripemd160_block", "ecrecover_base", "log_base", "log_byte",
    "storage_write_base", "storage_write_key_byte", "storage_write_value_byte",
    "storage_write_evicted_byte", "storage_read_base", "storage_read_key_byte",
    "storage_read_value_byte", "storage_remove_base", "storage_remove_key_byte",
    "storage_remove_ret_value_byte", "storage_has_key_base", "storage_has_key_byte",
    "storage_iter_create_prefix_base", "storage_iter_create_prefix_byte",
    "storage_iter_create_range_base", "storage_iter_create_from_byte",
    "storage_iter_create_to_byte", "storage_iter_next_base", "storage_iter_next_key_byte",
    "storage_iter_next_value_byte", "touching_trie_node", "read_cached_trie_node",
    "promise_and_base", "promise_and_per_promise", "promise_return", "validator_stake_base",
    "validator_total_stake_base", "alt_bn128_g1_multiexp_base", "alt_bn128_g1_multiexp_element",
    "alt_bn128_pairing_check_base", "alt_bn128_pairing_check_element", "alt_bn128_g1_sum_base",
    "alt_bn128_g1_sum_element", "ed25519_verify_base", "ed25519_verify_byte", "yield_create_base",
    "yield_create_byte", "yield_resume_base", "yield_resume_byte", "bls12381_p1_sum_base",
    "bls12381_p1_sum_element", "bls12381_p2_sum_base", "bls12381_p2_sum_element",
    "bls12381_g1_multiexp_base", "bls12381_g1_multiexp_element", "bls12381_g2_multiexp_base",
    "bls12381_g2_multiexp_element", "bls12381_map_fp_to_g1_base", "bls12381_map_fp_to_g1_element",
    "bls12381_map_fp2_to_g2_base", "bls12381_map_fp2_to_g2_element", "bls12381_pairing_base",
    "bls12381_pairing_element", "bls12381_p1_decompress_base", "bls12381_p1_decompress_element",
    "bls12381_p2_decompress_base", "bls12381_p2_decompress_element",
    "storage_large_read_overhead_base", "storage_large_read_overhead_byte", "p256_verify_base",
    "p256_verify_byte", "yield_create_with_id_base"]

/-- The profile of the runtime's gas split: each named cost at its index (a name the enums do not have is dropped). -/
def profileOf (p : Near.GasProfileSplit) : ProfileDataV3 :=
  let place (names : Array String) (size : Nat) (table : List (String × Nat)) : Array UInt64 :=
    table.foldl
      (fun (a : Array UInt64) (name, gas) =>
        match names.findIdx? (· == name) with
        | some i => a.modify i (· + gas.toUInt64)
        | none => a)
      (Array.replicate size 0)
  ⟨place actionCostNames 26 p.actions, place extCostNames 88 p.ext, p.wasm.toUInt64⟩

/-- `AccountContract` of the runtime's reference to a contract. `hashOfLabel` gives the 32 bytes of a code's hash name. -/
def contractOf (hashOfLabel : String → Option (List UInt8)) :
    Near.ContractRef → Except String AccountContract
  | .none => pure .none
  | .local h =>
    match hashOfLabel h with
    | some b => pure (.local ⟨ByteArray.mk b.toArray⟩)
    | none => throw s!"the code hash {h} is not a hash"
  | .global (.codeHash h) => pure (.global ⟨ByteArray.mk h.toArray⟩)
  | .global (.accountId id) => pure (.globalByAccount ⟨(String.fromUTF8? ⟨id.toArray⟩).getD ""⟩)

/-- The metadata of an outcome: `V1` for a transaction, `V4` for a receipt. -/
def metadataOf (hashOfLabel : String → Option (List UInt8)) (isTransaction : Bool)
    (o : Near.ExecutionOutcome) : Except String ExecutionMetadata := do
  if isTransaction then
    return .v1
  let contracts ← o.contracts.mapM (contractOf hashOfLabel)
  return .v4 ⟨profileOf o.profile, contracts.toArray⟩

end Near.Node.Chain
