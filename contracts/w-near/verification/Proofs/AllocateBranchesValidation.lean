import Proofs.AllocateValidation
import Proofs.AllocateFlaggedState

/-! Actual580 getter captures: empty, flags-two, one-hop and direct-fit paths. -/
namespace WNear.Proofs.AllocateBranchesValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

def flaggedMemory (memory : Memory) (head words : UInt32) : Memory := Id.run do
  let header := Allocate.splitHeader memory head words
  let mut m := writeI32 memory (header.toNat+8) 0
  m := writeI64 m header.toNat 0
  m := writeI32 m header.toNat (readI32 m head.toNat &&& 4294967292)
  m := writeI32 m (header.toNat+4) ((readI32 m (header.toNat+4) &&& 3)|||head)
  m := writeI32 m (head.toNat+8) (readI32 m (head.toNat+8) &&& 4294967294)
  m := writeI32 m head.toNat ((readI32 m head.toNat &&& 3)|||header)
  m := writeI32 m head.toNat (readI32 m head.toNat &&& 4294967293)
  m := writeI32 m header.toNat (readI32 m header.toNat |||2)
  m := writeI32 m header.toNat (readI32 m header.toNat |||1)
  return m

/-- Original-data split conditions, with no spare end backlink on flags-two. -/
def nativeSplit (memory : Memory) (head words : UInt32) (flags spare : Nat) : Bool :=
  decide memory.wf && decide (head≠0) && decide (0<words.toNat) &&
  decide (head.toNat+80+words.toNat*4≤(Allocate.endWord memory head).toNat) &&
  decide ((Allocate.endWord memory head).toNat+spare≤memory.byteSize) &&
  decide (readI32 memory head.toNat &&& 3=UInt32.ofNat flags) &&
  decide (readI32 memory (head.toNat+8) &&& 1=0)

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [580]
  let mut empty := 0
  let mut flagged := 0
  let mut skipped := 0
  let mut direct := 0
  for (_,entry) in ((seen.getD 580 #[]).filter (fun e=>e.1=="ft_total_supply")) do
    let memory := h.mem entry.store
    let words := UInt32.ofNat (u32Arg entry.args 0)
    let root := u32Arg entry.args 2
    let first := readI32 memory root
    let isEmpty := first==0
    let enough := words.toNat*4≤(Allocate.endWord memory first).toNat-first.toNat-8
    let hop := !isEmpty && !enough
    let head := if hop then readI32 memory (first.toNat+8) else first
    let before := if hop then writeI32 memory root head else memory
    let flags := readI32 before head.toNat &&& 3
    let isFlagged := !isEmpty && flags==2
    let expected := if isEmpty then memory else if isFlagged then flaggedMemory before head words
      else AllocateValidation.splitMemory before head words
    let pointer := if isEmpty then 0 else (Allocate.splitPointer before head words).toNat
    let gas := if isEmpty then 36 else if isFlagged then 277 else if hop then 344 else 273
    let steps := if isEmpty then 24 else if isFlagged then 239 else if hop then 295 else 236
    if u32Arg entry.args 1 != 1 then throw (IO.userError "unexpected getter580 alignment")
    if !isEmpty && flags != 0 && flags != 2 then throw (IO.userError "unexpected getter580 flags")
    if root+4>memory.byteSize || u32Arg entry.args 4+20>memory.byteSize then
      throw (IO.userError "getter580 original root/vtable bound mismatch")
    if !isEmpty && !nativeSplit before head words (if isFlagged then 2 else 0) (if isFlagged then 0 else 8) then
      throw (IO.userError "getter580 original split Native conditions failed")
    if hop then
      let nextSep := root+4≤head.toNat || head.toNat+12≤root
      let vtable := u32Arg entry.args 4
      let vtableSep := root+4≤vtable+16 || vtable+20≤root
      if !(nextSep && vtableSep) then throw (IO.userError "getter580 skip original root separation mismatch")
    let result := h.call entry.store 580 entry.args
    if returnsU32 result != some pointer then throw (IO.userError "getter580 pointer mismatch")
    if result.gas != op h gas then throw (IO.userError "getter580 exact gas mismatch")
    if (h.mem result.after).pages != expected.pages || (h.mem result.after).max != expected.max then
      throw (IO.userError "getter580 exact sequential memory mismatch")
    if h.global result.after 0 != h.global entry.store 0 then throw (IO.userError "getter580 changed SP")
    let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[580]! entry.args
      | throw (IO.userError "getter580 start failed")
    let active := (chargeWasm (.next initial) (entryCost h.cfg.wasm (.next initial))).1
    let fuel := AllocateValidation.fuelUsed h.cfg.wasm active
    if fuel != steps then throw (IO.userError s!"getter580 step mismatch got{fuel}/expected{steps}")
    match (runInitialized h.cfg.wasm (fuel-1) (.next initial)).2 with
    | some (.executionIssue .fuelExhausted) => pure ()
    | _ => throw (IO.userError "getter580 one-less-fuel mismatch")
    if isEmpty then empty:=empty+1 else if isFlagged then flagged:=flagged+1
      else if hop then skipped:=skipped+1 else direct:=direct+1
    IO.println s!"PASS actual getter580 words={words.toNat},empty={isEmpty},flags={flags.toNat},skipped={hop}: {gas} root gas units/{steps} steps; exact whole memory/SP/pointer"
  if (empty,flagged,skipped,direct)!=(1,1,1,2) then
    throw (IO.userError s!"unexpected getter580 coverage {empty}/{flagged}/{skipped}/{direct}")
#eval validate
end WNear.Proofs.AllocateBranchesValidation
