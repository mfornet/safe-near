import NearNode.Rpc.Methods
import NearNode.Chain.FastEngine

/-!
# `query`

`RpcQueryRequest` (`chain/jsonrpc-primitives/src/types/query.rs`): the `request_type` selects the view
(`view_account`, `view_code`, `view_state`, `view_access_key`, `view_access_key_list`), the block is named
by `finality`, `block_id` or `sync_checkpoint`; the answer carries `block_height` and `block_hash` next to
the view. A key that does not exist is an answer (with an `error` member), as `process_query_response`
makes it; the other failures are handler errors.
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Network Near.Node.Validator
  Near.Node.Apply

/-- `BlockReference` as the Rust `Debug` of an unknown block names it in the message. -/
private def refJson : BlockRef → Json
  | .optimistic => Json.mkObj [("finality", "optimistic")]
  | .nearFinal => Json.mkObj [("finality", "near-final")]
  | .final => Json.mkObj [("finality", "final")]
  | .height h => Json.mkObj [("block_id", jn h)]
  | .hash h => Json.mkObj [("block_id", jhash h)]
  | .genesis => Json.mkObj [("sync_checkpoint", "genesis")]
  | .earliest => Json.mkObj [("sync_checkpoint", "earliest_available")]

private def refDebug : BlockRef → String
  | .optimistic => "Finality(None)"
  | .nearFinal => "Finality(DoomSlug)"
  | .final => "Finality(Final)"
  | .height h => s!"BlockId(Height({h}))"
  | .hash h => s!"BlockId(Hash({base58Encode h.bytes}))"
  | .genesis => "SyncCheckpoint(Genesis)"
  | .earliest => "SyncCheckpoint(EarliestAvailable)"

private def queryUnknownBlock (s : VState) (params : Json) (r : BlockRef) : RpcError :=
  let data : String :=
    match r with
    | .height h => s!"DB Not Found Error: BLOCK HEIGHT: {h} \n Cause: Unknown"
    | .hash h => s!"DB Not Found Error: BLOCK HEADER: {base58Encode h.bytes}"
    | _ =>
      s!"Block either has never been observed on the node or has been garbage collected: {refDebug r}"
  RpcError.handler "UNKNOWN_BLOCK" (some (Json.mkObj [("block_reference", refJson r)]))
    (Json.str data) (unknownBlockStatus s params)

private def blockInfo (b : BlockRec) : List (String × Json) :=
  [("block_height", jn b.view.height.toNat), ("block_hash", jhash b.hash)]

private def blockInfoJson (b : BlockRec) : Json :=
  Json.mkObj [("block_height", jn b.view.height.toNat), ("block_hash", jhash b.hash)]

private def withBlock (b : BlockRec) (fields : List (String × Json)) : R :=
  .ok (Json.mkObj (fields ++ blockInfo b))

private def unknownAccount (b : BlockRec) (a : AccountId) : RpcError :=
  RpcError.handler "UNKNOWN_ACCOUNT"
    (some (Json.mkObj ([("requested_account_id", jacc a)] ++ blockInfo b)))
    (Json.str s!"account {a.val} does not exist while viewing")

private def internalError (m : String) : RpcError :=
  RpcError.internal m

/-- Parses the `request` members of a query. -/
inductive QueryRequest where
  | account (a : AccountId)
  | code (a : AccountId)
  |
  state (a : AccountId) (prefix_ : ByteArray) (after : Option ByteArray) (limit : Option Nat)
    (proof : Bool)
  | accessKey (a : AccountId) (k : PublicKey)
  | accessKeys (a : AccountId)
  | call (a : AccountId) (method : String) (args : ByteArray)
  /-- `ViewGlobalContractCode` and `ViewGlobalContractCodeByAccountId`. -/
  | globalCode (id : GlobalContractIdentifier)

private def b64Field (o : Json) (k : String) : Except String ByteArray :=
  match field? o k with
  | some (.str s) =>
    match base64Decode s with
    | .ok b => pure b
    | .error why => throw why
  | _ => throw s!"missing field `{k}`"

private def accountField (o : Json) : Except String AccountId :=
  match field? o "account_id" with
  | some j => parseAccount j
  | none => throw "missing field `account_id`"

def parseRequest (o : Json) : Except String QueryRequest := do
  let some (.str t) := field? o "request_type" | throw "missing field `request_type`"
  match t with
  | "view_account" =>
    pure (.account (← accountField o))
  | "view_code" =>
    pure (.code (← accountField o))
  | "view_access_key_list" =>
    pure (.accessKeys (← accountField o))
  | "view_access_key" =>
    let a ← accountField o
    let some k := field? o "public_key" | throw "missing field `public_key`"
    pure (.accessKey a (← parseKey k))
  | "view_state" =>
    let a ← accountField o
    let p ← b64Field o "prefix_base64"
    let after ←
      if hasField o "after_key_base64" then
        some <$> b64Field o "after_key_base64"
      else
        pure none
    let limit ←
      match field? o "limit" with
      | some j =>
        some <$> parseU64 j
      | none =>
        pure none
    let proof := (field? o "include_proof") == some (Json.bool true)
    if proof && (after.isSome || limit.isSome) then
      throw "include_proof is not supported with paginated view_state (after_key_base64 / limit)"
    if let some k := after then
      unless k.size ≥ p.size && k.extract 0 p.size == p do
        throw "after_key_base64 must start with prefix_base64"
    pure (.state a p after limit proof)
  | "call_function" =>
    let a ← accountField o
    let some (.str m) := field? o "method_name" | throw "missing field `method_name`"
    pure (.call a m (← b64Field o "args_base64"))
  | "view_global_contract_code" =>
    let some h := field? o "code_hash" | throw "missing field `code_hash`"
    match h with
    | .str _ =>
      pure (.globalCode (.codeHash (← parseHash h)))
    | _ =>
      throw s!"invalid type: {serdeFound h}, expected base58-encoded 256-bit hash"
  | "view_global_contract_code_by_account_id" =>
    pure (.globalCode (.accountId (← accountField o)))
  | other =>
    throw
        s!"unknown variant `{other}`, expected one of `view_account`, `view_code`, `view_state`, `view_access_key`, `view_access_key_list`, `view_gas_key_nonces`, `call_function`, `view_global_contract_code`, `view_global_contract_code_by_account_id`"

/-- The `Debug` text of nearcore's `VMError`, as the message of a failed view call carries it
(`wasm execution failed with error: {err:?}`), for the errors a view call meets most; the others carry the
model's message. -/
private def vmErrorText (e : Wasm.Near.FunctionCallError) : String :=
  let debug : String :=
    match e with
    | .methodResolveError .methodNotFound => "MethodResolveError(MethodNotFound)"
    | .methodResolveError .methodEmptyName => "MethodResolveError(MethodEmptyName)"
    | .methodResolveError .methodInvalidSignature => "MethodResolveError(MethodInvalidSignature)"
    | .wasmTrap .unreachable => "WasmTrap(Unreachable)"
    | .wasmTrap .incorrectCallIndirectSignature => "WasmTrap(IncorrectCallIndirectSignature)"
    | .wasmTrap .memoryOutOfBounds => "WasmTrap(MemoryOutOfBounds)"
    | .wasmTrap .callIndirectOOB => "WasmTrap(CallIndirectOOB)"
    | .wasmTrap .illegalArithmetic => "WasmTrap(IllegalArithmetic)"
    | .wasmTrap .misalignedAtomicAccess => "WasmTrap(MisalignedAtomicAccess)"
    | .wasmTrap .indirectCallToNull => "WasmTrap(IndirectCallToNull)"
    | .wasmTrap .stackOverflow => "WasmTrap(StackOverflow)"
    | .wasmTrap .genericTrap => "WasmTrap(GenericTrap)"
    | .hostError .gasExceeded => "HostError(GasExceeded)"
    | .hostError .gasLimitExceeded => "HostError(GasLimitExceeded)"
    | .hostError (.prohibitedInView m) =>
      s!"HostError(ProhibitedInView \{ method_name: {stringDebug m} })"
    | .hostError (.guestPanic m) => s!"HostError(GuestPanic \{ panic_msg: {stringDebug m} })"
    | other => other.message
  s!"wasm execution failed with error: {debug}"

/-- Runs a function of a contract as a view (`TrieViewer::call_function`): the account calls itself with no deposit
and the gas limit of a view, on the state the block left. -/
def callFunction (c : Ctx) (s : VState) (view : StateAt) (b : BlockRec) (a : AccountId)
    (method : String) (args : ByteArray) : R :=
  let cfg := c.env.params.cfg
  match view.account a with
  | .error m => .error (internalError m)
  | .ok none => .error (unknownAccount b a)
  | .ok (some acc) =>
    let codeKey : Option TrieKey :=
      match acc with
      | .v1 .. => acc.localHash.map fun _ => .contractCode a
      | .v2 _ _ _ (.local _) => some (.contractCode a)
      | .v2 _ _ _ (.global h) => some (.globalContractCode (.codeHash h))
      | .v2 _ _ _ (.globalByAccount id) => some (.globalContractCode (.accountId id))
      | .v2 _ _ _ .none => none
    let _noCode : RpcError :=
      RpcError.handler "NO_CONTRACT_CODE"
        (some (Json.mkObj ([("contract_account_id", jacc a)] ++ blockInfo b)))
        (Json.str s!"Contract code for contract ID #{a.val} has never been observed on the node")
    let compilation : R :=
      .ok
        (Json.mkObj
          ([("error",
                Json.str
                  s!"wasm execution failed with error: CompilationError(CodeDoesNotExist \{ account_id: {stringDebug a.val} })"),
              ("logs", Json.arr #[])] ++
            blockInfo b))
    match codeKey with
    | none => compilation
    | some key =>
      match view.get key with
      | .error m => .error (internalError m)
      | .ok none => compilation
      | .ok (some blob) =>
        match (Apply.code blob).run {} with
        | .error m => .error (internalError m)
        | .ok (loaded, _) =>
          match view.contractData a ByteArray.empty with
          | .error m => .error (internalError m)
          | .ok items =>
            let storage := items.toList.map fun (k, v) => (k.toList, v.toList)
            let (amount, locked, usage) :=
              match acc with
              | .v1 am lo _ us => (am, lo, us)
              | .v2 am lo us _ => (am, lo, us)
            let bytes (id : AccountId) : List UInt8 := id.val.toUTF8.toList
            let gas := cfg.wasm.limits.maxGasBurnt
            let epochHeight :=
              ((s.st.epoch b.view.epochId).toOption.map (·.info.view.epochHeight)).getD 0
            let ctx : Wasm.Near.VMContext :=
              { currentAccountId := bytes a, signerAccountId := bytes a,
                signerAccountPk :=
                  (Codec.encode (PublicKey.ed25519 (ByteArray.mk (Array.replicate 32 0)))).toList,
                predecessorAccountId := bytes a, input := args.toList,
                blockHeight := b.view.height.toNat, blockTimestamp := b.view.timestamp.toNat,
                epochHeight, accountBalance := amount.val, accountLockedBalance := locked.val,
                storageUsage := usage.toNat, attachedDeposit := 0, prepaidGas := gas,
                randomSeed := view.root.bytes.toList, viewConfig := some { maxGasBurnt := gas },
                chargeStorageValueAccess := true, chainId := c.env.params.chainId.toUTF8.toList }
            let outcome :=
              Near.VmEngine.run cfg loaded.code.module loaded.code.size method ctx storage
            match outcome.aborted with
            | some err =>
              .ok
                (Json.mkObj
                  ([("error", Json.str (vmErrorText err)), ("logs", Json.arr #[])] ++ blockInfo b))
            | none =>
              let result : List UInt8 :=
                match outcome.returnData with
                | .value v => v
                | _ => []
              .ok
                (Json.mkObj
                  ([("result", Json.arr (result.toArray.map fun x => jn x.toNat)),
                      ("logs", jarr Json.str outcome.logs.toArray)] ++
                    blockInfo b))

def query (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  let parsed : Except String (BlockRef × QueryRequest) := do
    match params with
    | .obj _ =>
      pure ()
    | .null =>
      throw "invalid type: null, expected string or map"
    | _ =>
      throw "invalid type, expected a map"
    let ref ← parseBlockRef params (flattened := true)
    pure (ref, ← parseRequest params)
  match liftParse parsed with
  | .error e =>
    return .error e
  | .ok (ref, req) =>
    let some b := resolve s ref | return .error (queryUnknownBlock s params ref)
    let viewOf : Except String StateAt :=
      match req with
      | .account a | .code a | .state a .. | .accessKey a _ | .accessKeys a | .call a .. =>
        stateAt s b a
      | .globalCode _ => stateAtFirstShard s b
    let view ←
      match viewOf with
      | .ok v =>
        pure v
      | .error m =>
        return .error (internalError m)
    match req with
    | .account a =>
      match view.account a with
      | .error m =>
        return .error (internalError m)
      | .ok none =>
        return .error (unknownAccount b a)
      | .ok (some acc) =>
        match accountView acc with
        | .obj kvs =>
          return withBlock b (kvs.toList.map fun (k, v) => (k, v))
        | j =>
          return .ok j
    | .code a =>
      match view.account a with
      | .error m =>
        return .error (internalError m)
      | .ok none =>
        return .error (unknownAccount b a)
      | .ok (some acc) =>
        let noCode : RpcError :=
          RpcError.handler "NO_CONTRACT_CODE"
            (some (Json.mkObj ([("contract_account_id", jacc a)] ++ blockInfo b)))
            (Json.str
              s!"Contract code for contract ID #{a.val} has never been observed on the node")
        -- `view_account_contract_code`: the code the account holds, or the global contract it uses
        let found : Except String (Option (ByteArray × CryptoHash)) :=
          match acc with
          | .v2 _ _ _ (.global h) =>
            (view.get (.globalContractCode (.codeHash h))).map fun c => c.map (·, h)
          | .v2 _ _ _ (.globalByAccount id) =>
            (view.get (.globalContractCode (.accountId id))).map fun c =>
              c.map fun code => (code, CryptoHash.hash code)
          | _ =>
            match acc.localHash with
            | some h => (view.get (.contractCode a)).map fun c => c.map (·, h)
            | none => pure none
        match found with
        | .error m =>
          return .error (internalError m)
        | .ok (some (code, h)) =>
          return withBlock b [("code_base64", jbytes code), ("hash", jhash h)]
        | .ok none =>
          return .error noCode
    | .globalCode id =>
      let key : GlobalContractCodeIdentifier :=
        match id with
        | .codeHash h => .codeHash h
        | .accountId a => .accountId a
      match view.get (.globalContractCode key) with
      | .error m =>
        return .error (internalError m)
      | .ok (some code) =>
        let h : CryptoHash :=
          match id with
          | .codeHash h => h
          | .accountId _ => CryptoHash.hash code
        return withBlock b [("code_base64", jbytes code), ("hash", jhash h)]
      | .ok none =>
        let (key, debug) : String × String :=
          match id with
          | .codeHash h => ("hash", s!"CodeHash({base58Encode h.bytes})")
          | .accountId a => ("account_id", s!"AccountId(AccountId({stringDebug a.val}))")
        let idJson : Json :=
          match id with
          | .codeHash h => Json.mkObj [(key, jhash h)]
          | .accountId a => Json.mkObj [(key, jacc a)]
        return .error
            (RpcError.handler "NO_GLOBAL_CONTRACT_CODE"
              (some (Json.mkObj ([("identifier", idJson)] ++ blockInfo b)))
              (Json.str
                s!"Global contract code with identifier {debug} has never been observed on the node"))
    | .accessKey a k =>
      match view.accessKey a k with
      | .error m =>
        return .error (internalError m)
      | .ok (some key) =>
        withBlock b
              [("nonce", jn key.nonce.toNat), ("permission", permissionView key.permission)] |>
            pure
      | .ok none =>
        return withBlock b
            [("error", Json.str s!"access key {k.toText} does not exist while viewing"),
              ("logs", Json.arr #[])]
    | .accessKeys a =>
      match view.accessKeys a with
      | .error m =>
        return .error (internalError m)
      | .ok keys =>
        withBlock b
              [("keys",
                  jarr
                    (fun (kk : PublicKey × AccessKey) =>
                      Json.mkObj [("public_key", jkey kk.1), ("access_key", accessKeyView kk.2)])
                    keys)] |>
            pure
    | .state a p after limit _ =>
      match view.account a with
      | .error m =>
        return .error (internalError m)
      | .ok none =>
        return .error (unknownAccount b a)
      | .ok (some _) =>
        match view.contractData a p with
        | .error m =>
          return .error (internalError m)
        | .ok items =>
          let items :=
            match after with
            | some k => items.filter fun (key, _) => !(bytesLt key k) && key != k
            | none => items
          let page :=
            match limit with
            | some n => items.extract 0 n
            | none => items
          let last : List (String × Json) :=
            match limit with
            | some n => if items.size > n then [("last_key", jbytes (page.back!.1))] else []
            | none => []
          withBlock b
                ([("values",
                      jarr
                        (fun (kv : ByteArray × ByteArray) =>
                          Json.mkObj [("key", jbytes kv.1), ("value", jbytes kv.2)])
                        page)] ++
                  last) |>
              pure
    | .call a method args =>
      return callFunction c s view b a method args

end Near.Node.Rpc
