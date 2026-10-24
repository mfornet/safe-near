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

def applyCharge (ns : NearState) : Charge → NearState × Option HostError
  | .ext name times =>
    let (g, e) := ns.gas.burn (ns.extCosts.cost name * times)
    ({ ns with gas := g, gasProfile := ns.gasProfile.addExt name (g.burnt - ns.gas.burnt) }, e)
  | .burn n =>
    let (g, e) := ns.gas.burn n
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)
  | .actionBase fee sir =>
    let f := fee ns.fees
    let (g, e) := ns.gas.payAction (f.send sir) f.execution
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)
  | .actionBytes fee n sir =>
    let f := fee ns.fees
    let (g, e) := ns.gas.payAction (f.send sir * n) (f.execution * n)
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)
  | .newReceipt sir depsSir =>
    let a := ns.fees.newActionReceipt
    let d := ns.fees.newDataReceiptBase
    -- Both sending and executing dependency data receipts are burnt here,
    -- rather than reserving their execution fee for the callback runtime.
    let burn := a.send sir + (depsSir.map fun s => d.send s + d.execution).sum
    let use := a.execution
    let (g, e) := ns.gas.payAction burn use
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)
  | .prepay n =>
    let (g, e) := ns.gas.prepay n
    ({ ns with gas := g }, e)
  | .pay burn execution =>
    let (g, e) := ns.gas.payAction burn execution
    ({ ns with gas := g, gasProfile := { ns.gasProfile with
      actionBurnt := ns.gasProfile.actionBurnt + (g.burnt - ns.gas.burnt) } }, e)

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

def readMem (n : Nat) : List Charge := [.ext "read_memory_base", .ext "read_memory_byte" n]
def writeMem (n : Nat) : List Charge := [.ext "write_memory_base", .ext "write_memory_byte" n]
def writeReg (n : Nat) : List Charge := [.ext "write_register_base", .ext "write_register_byte" n]
def utf8 (n : Nat) : List Charge := [.ext "utf8_decoding_base", .ext "utf8_decoding_byte" n]
def utf16 (n : Nat) : List Charge := [.ext "utf16_decoding_base", .ext "utf16_decoding_byte" n]

def spanReadError (len ptr : UInt64) : HostError :=
  if len == u64Max then .invalidRegisterId ptr.toNat else .memoryAccessViolation

end Wasm.Near
