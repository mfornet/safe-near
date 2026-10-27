import NearVM.MeteredMemoryRules
import Harness.Main
import Proofs.AllocateNative

/-! Reproducible positive malloc captures and the actual sequential end split.
This validation does not assert a kernel WP for the still-open search loop. -/
namespace WNear.Proofs.AllocateValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing
open Allocate

/-- Exact writes of the captured no-growth, low-flags-zero split path. The
backlink loads deliberately use each current memory. -/
def splitMemory (memory : Memory) (head words : UInt32) : Memory := Id.run do
  let header := splitHeader memory head words
  let finish := endWord memory head
  let mut result := writeI32 memory (header.toNat+8) 0
  result := writeI64 result header.toNat 0
  result := writeI32 result header.toNat (readI32 result head.toNat &&& 4294967292)
  result := writeI32 result (finish.toNat+4) ((readI32 result (finish.toNat+4) &&& 3) ||| header)
  result := writeI32 result (header.toNat+4) ((readI32 result (header.toNat+4) &&& 3) ||| head)
  result := writeI32 result (head.toNat+8) (readI32 result (head.toNat+8) &&& 4294967294)
  result := writeI32 result head.toNat ((readI32 result head.toNat &&& 3) ||| header)
  result := writeI32 result header.toNat (readI32 result header.toNat ||| 1)
  return result

def native (memory : Memory) (head words : UInt32) : Bool :=
  decide memory.wf && decide (0<words.toNat) &&
  decide (head.toNat+80+words.toNat*4 ≤ (endWord memory head).toNat) &&
  decide ((endWord memory head).toNat+8 ≤ memory.byteSize) &&
  decide (readI32 memory head.toNat &&& 3 = 0) &&
  decide (readI32 memory (head.toNat+8) &&& 1 = 0)

def fuelUsed (cfg : WasmConfig) (machine : Machine) : Nat := Id.run do
  let mut m := machine
  for n in [0:2000] do
    match m with
    | .next _ => m := (runMetered cfg 1 m).1
    | _ => return n
  return 2000

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [581,580]
  let mut checked := 0
  let mut outside := 0
  for (_,entry) in ((seen.getD 580 #[]).filter (fun e=>e.1=="ft_total_supply")) do
    let memory := h.mem entry.store
    let words := UInt32.ofNat (u32Arg entry.args 0)
    let root := u32Arg entry.args 2
    let first := readI32 memory root
    if first == 0 then continue
    let enough := words.toNat*4 ≤ (endWord memory first).toNat-first.toNat-8
    let head := if enough then first else readI32 memory (first.toNat+8)
    let before := if enough then memory else writeI32 memory root head
    if !native before head words then
      outside := outside+1
      continue
    let result := h.call entry.store 580 entry.args
    if returnsU32 result != some (splitPointer before head words).toNat then
      throw (IO.userError "actual allocation result differs from original-header split pointer")
    let expected := splitMemory before head words
    if (h.mem result.after).pages != expected.pages || (h.mem result.after).max != expected.max then
      throw (IO.userError "actual allocation memory differs from complete sequential split")
    let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[580]! entry.args
      | throw (IO.userError "f580 start failed")
    let active := (chargeWasm (.next initial) (entryCost h.cfg.wasm (.next initial))).1
    let fuel := fuelUsed h.cfg.wasm active
    match (runInitialized h.cfg.wasm (fuel-1) (.next initial)).2 with
    | some (.executionIssue .fuelExhausted) => pure ()
    | _ => throw (IO.userError "f580 one-less-fuel mismatch")
    IO.println s!"PASS f580 original-header split words={words.toNat}: gas={result.gas/(op h 1)}, fuel={fuel}, skipped={if enough then 0 else 1}; full memory and nonzero pointer"
    checked := checked+1
  if checked != 3 || outside != 1 then throw (IO.userError s!"expected three low-flags-zero getter splits and one flags-two split, got {checked}/{outside}")
  IO.println "SCOPE: the grow/flags-two allocation is recorded outside this no-growth split contract"
#eval validate
end WNear.Proofs.AllocateValidation
