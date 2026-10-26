import NearVM.State

/-!
# Gas charges

One gas charge of a host function, and the charges of reading and writing the arguments of the
host functions. They are shared by the metered wrappers (`NearVM.Metered`) and by the
cryptographic host functions (`NearVM.CryptoHost`), which compute their own charges.
-/

namespace Wasm.Near

/-- One gas charge. -/
inductive Charge
  /-- `times` × the named `ExtCosts` entry, burnt. -/
  | ext (name : String) (times : Nat := 1)
  | burn (gas : Nat)
  /-- `pay_action_base`. -/
  | actionBase (fee : ActionFees → Fee) (sir : Bool)
  /-- `pay_action_per_byte`. -/
  | actionBytes (fee : ActionFees → Fee) (n : Nat) (sir : Bool)
  /-- `pay_gas_for_new_receipt`: one action receipt plus one data receipt per dependency. -/
  | newReceipt (sir : Bool) (depsSir : List Bool)
  /-- `prepay_gas`: gas attached to a function call action. -/
  | prepay (gas : Nat)
  /-- `pay_action_accumulated(burn, burn + execution)`: a send cost burnt now with the
  execution cost it obliges, when neither is a plain per-byte multiple of one fee. -/
  | pay (burn execution : Nat)

/-- `near_parameters::ActionCosts` by name, in the order of `ActionFees`' fields. -/
def actionCostNames : List String :=
  ["create_account", "delete_account", "deploy_contract_base", "deploy_contract_byte",
    "function_call_base", "function_call_byte", "transfer", "stake", "add_full_access_key",
    "add_function_call_key_base", "add_function_call_key_byte", "delete_key", "new_action_receipt",
    "new_data_receipt_base", "new_data_receipt_byte", "delegate", "use_global_contract_base",
    "use_global_contract_byte", "deploy_global_contract_base", "deploy_global_contract_byte",
    "gas_key_transfer_base", "gas_key_byte", "gas_key_nonce_write_base"]

/-- A fee table in which entry number `k` carries `2 ^ k` as its send fee. A charge names the entry it pays by a selector
(`ActionFees → Fee`), possibly a sum of entries (a transfer to an implicit account also pays for the account and its
key); reading the selector's answer in this table tells which `ActionCosts` entries it stands for, without changing how
charges are written. -/
def costProbe : ActionFees :=
  { createAccount := { sendSir := 1 }, deleteAccount := { sendSir := 2 },
    deployContractBase := { sendSir := 4 }, deployContractByte := { sendSir := 8 },
    functionCallBase := { sendSir := 16 }, functionCallByte := { sendSir := 32 },
    transfer := { sendSir := 64 }, stake := { sendSir := 128 },
    addFullAccessKey := { sendSir := 256 }, addFunctionCallKeyBase := { sendSir := 512 },
    addFunctionCallKeyByte := { sendSir := 1024 }, deleteKey := { sendSir := 2048 },
    newActionReceipt := { sendSir := 4096 }, newDataReceiptBase := { sendSir := 8192 },
    newDataReceiptByte := { sendSir := 16384 }, delegate := { sendSir := 32768 },
    useGlobalContractBase := { sendSir := 65536 }, useGlobalContractByte := { sendSir := 131072 },
    deployGlobalContractBase := { sendSir := 262144 },
    deployGlobalContractByte := { sendSir := 524288 }, gasKeyTransferBase := { sendSir := 1048576 },
    gasKeyByte := { sendSir := 2097152 }, gasKeyNonceWriteBase := { sendSir := 4194304 } }

/-- The `ActionCosts` name a fee selector stands for: `transfer` when the selector includes the transfer fee (nearcore
profiles the whole payment of a transfer under it), otherwise its first entry. -/
def actionCostName (fee : ActionFees → Fee) : String :=
  let v := (fee costProbe).sendSir
  if v.testBit 6 then "transfer"
  else (actionCostNames.zipIdx.find? fun (_, k) => v.testBit k).elim "unknown" (·.1)

/-- Observational: add `amount` burnt gas to the profile of the action cost `name` (nothing for zero). -/
def addActionCost (profile : List (String × Nat)) (name : String) (amount : Nat) :
    List (String × Nat) :=
  if amount == 0 then profile
  else
    let previous := ((profile.find? (·.1 == name)).map (·.2)).getD 0
    (name, previous + amount) :: profile.filter (·.1 != name)

/-- Observational: the state with `amount` burnt gas added to the profile of the action cost `name`. Only the profile
changes, so the gas counter and everything else are as they were. -/
def _root_.Wasm.NearState.profileAction (ns : NearState) (name : String) (amount : Nat) :
    NearState :=
  { ns with actionProfile := addActionCost ns.actionProfile name amount }

def applyCharge (ns : NearState) : Charge → NearState × Option HostError
  | .ext name times =>
    let (g, e) := ns.gas.burn (ns.extCosts.cost name * times)
    ({ ns with
        gas := g, gasProfile := ns.gasProfile.addExt name (g.burnt - ns.gas.burnt) },
      e)
  | .burn n =>
    let (g, e) := ns.gas.burn n
    (({ ns with
            gas := g,
            gasProfile :=
              { ns.gasProfile with
                actionBurnt :=
                  ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }).profileAction
        "new_data_receipt_byte" (g.burnt - ns.gas.burnt),
      e)
  | .actionBase fee sir =>
    let f := fee ns.fees
    let (g, e) := ns.gas.payAction (f.send sir) f.execution
    (({ ns with
            gas := g,
            gasProfile :=
              { ns.gasProfile with
                actionBurnt :=
                  ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }).profileAction
        (actionCostName fee) (g.burnt - ns.gas.burnt),
      e)
  | .actionBytes fee n sir =>
    let f := fee ns.fees
    let (g, e) := ns.gas.payAction (f.send sir * n) (f.execution * n)
    (({ ns with
            gas := g,
            gasProfile :=
              { ns.gasProfile with
                actionBurnt :=
                  ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }).profileAction
        (actionCostName fee) (g.burnt - ns.gas.burnt),
      e)
  | .newReceipt sir depsSir =>
    let a := ns.fees.newActionReceipt
    let d := ns.fees.newDataReceiptBase
    -- Both sending and executing dependency data receipts are burnt here,
    -- rather than reserving their execution fee for the callback runtime.
    let burn := a.send sir + (depsSir.map fun s => d.send s + d.execution).sum
    let use := a.execution
    let (g, e) := ns.gas.payAction burn use
    -- nearcore pays the data receipts' base fees together with the action receipt's and profiles them under it
    (({ ns with
            gas := g,
            gasProfile :=
              { ns.gasProfile with
                actionBurnt :=
                  ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }).profileAction
        "new_action_receipt" (g.burnt - ns.gas.burnt),
      e)
  | .prepay n =>
    let (g, e) := ns.gas.prepay n
    ({ ns with gas := g }, e)
  | .pay burn execution =>
    let (g, e) := ns.gas.payAction burn execution
    -- the only send fee paid this way is `gas_key_byte`; the execution-only payment of the nonce rows burns nothing
    (({ ns with
            gas := g,
            gasProfile :=
              { ns.gasProfile with
                actionBurnt :=
                  ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }).profileAction
        "gas_key_byte" (g.burnt - ns.gas.burnt),
      e)

def applyCharges (ns : NearState) : List Charge → NearState × Option HostError
  | [] => (ns, none)
  | c :: cs =>
    match applyCharge ns c with
    | (ns', none) => applyCharges ns' cs
    | (ns', some e) => (ns', some e)

/-! ## Cost rules -/

def argU64 (args : List Value) (i : Nat) : UInt64 :=
  match args[i]? with
  | some (.i64 n) => n
  | _ => 0

/-- Bytes of a `(len, ptr)` argument following `get_memory_or_register`. -/
def spanLen (st : HostStore NearState) (len ptr : UInt64) : Nat :=
  if len = u64Max then ((st.host.registers ptr.toNat).map List.length).getD 0 else len.toNat

/-- Reading a `(len, ptr)` argument: memory or register costs. -/
def readSpan (st : HostStore NearState) (len ptr : UInt64) : List Charge :=
  if len = u64Max then
    match st.host.registers ptr.toNat with
    | none => []
    | some bytes => [.ext "read_register_base", .ext "read_register_byte" bytes.length]
  else [.ext "read_memory_base", .ext "read_memory_byte" len.toNat]

def readMem (n : Nat) : List Charge :=
  [.ext "read_memory_base", .ext "read_memory_byte" n]

def writeMem (n : Nat) : List Charge :=
  [.ext "write_memory_base", .ext "write_memory_byte" n]

def writeReg (n : Nat) : List Charge :=
  [.ext "write_register_base", .ext "write_register_byte" n]

def utf8 (n : Nat) : List Charge :=
  [.ext "utf8_decoding_base", .ext "utf8_decoding_byte" n]

def utf16 (n : Nat) : List Charge :=
  [.ext "utf16_decoding_base", .ext "utf16_decoding_byte" n]

def spanReadError (len ptr : UInt64) : HostError :=
  if len == u64Max then .invalidRegisterId ptr.toNat else .memoryAccessViolation

end Wasm.Near
