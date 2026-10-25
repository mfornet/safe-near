import NearVM
import Wasm.Wat

/-!
# `log_utf8`, `log_utf16`, `panic_utf8` and `abort` under `NearVM.run`

The messages are decoded as nearcore does (UTF-16LE to UTF-8 with surrogate pairs, UTF-8
validation), and the gas is paid in nearcore's order: the decoding byte cost on the raw length,
`log_byte` on the decoded length, and nothing after the first error. Each case runs a Wasm module
that makes one call.
-/

open Wasm Wasm.Near

namespace LogHosts

private def hex2 (b : UInt8) : String :=
  let digits := Nat.toDigits 16 b.toNat
  String.join ((if digits.length < 2 then '0' :: digits else digits).map String.singleton)

private def esc (bytes : List UInt8) : String :=
  String.join (bytes.map fun b => "\\" ++ hex2 b)

/-- Memory holding `mem` at address 0; `name` is called with the constants `args`. -/
private def build (name : String) (ints : Bool) (mem : List UInt8) (args : List Int) : IO Module := do
  let ty := if ints then "i32" else "i64"
  let params := String.intercalate " " (List.replicate args.length ty)
  let pushed := String.intercalate " " (args.map fun a => s!"{ty}.const {a}")
  let text :=
    s!"(module (import \"env\" \"{name}\" (func $f (param {params})))
    (memory 1) (data (i32.const 0) \"{esc mem}\") (func (export \"test\") {pushed} call $f))"
  match ← Wat.compile text with
  | .ok module => pure module
  | .error error => throw (IO.userError s!"log fixture {name}: {error}")

private def bytesOf (s : String) : List UInt8 := s.toUTF8.toList

private def context : VMContext :=
  { currentAccountId := "log.near".toUTF8.toList
    signerAccountId := "alice.near".toUTF8.toList
    signerAccountPk := 0 :: List.replicate 32 1
    predecessorAccountId := "alice.near".toUTF8.toList
    input := [], prepaidGas := 300 * 10 ^ 12 }

private def cost (outcome : VMOutcome) (name : String) : Nat :=
  ((outcome.gasProfile.ext.find? (·.1 == name)).map (·.2)).getD 0

private def failsWith (outcome : VMOutcome) (message : HostError) : Bool :=
  outcome.aborted == some (.hostError message)

/-- UTF-16LE of the code units. -/
private def units (us : List Nat) : List UInt8 :=
  us.flatMap fun u => [UInt8.ofNat (u % 256), UInt8.ofNat (u / 256)]

private def u32le (n : Nat) : List UInt8 := (List.range 4).map fun i => UInt8.ofNat (n / 256 ^ i % 256)

def check (cfg : RuntimeConfig) (check : String → Bool → IO Unit) : IO Unit := do
  let price := cfg.wasm.extCosts.cost
  let exec (module : Module) (config : RuntimeConfig := cfg) : VMOutcome :=
    run config module 0 "test" context []
  let log16 (mem : List UInt8) (args : List Int) := build "log_utf16" false mem args
  let log8 (mem : List UInt8) (args : List Int) := build "log_utf8" false mem args
  let limited (maxTotal maxCount : Nat) :=
    { cfg with wasm := { cfg.wasm with limits :=
      { cfg.wasm.limits with maxTotalLogLength := maxTotal, maxNumberLogs := maxCount } } }
  -- log_utf16
  let hello := units ("hello".toList.map Char.toNat)
  let o := exec (← log16 hello [10, 0])
  check "log_utf16: ASCII is stored as UTF-8"
    (o.succeeded && o.logs == ["hello"])
  check "log_utf16: ASCII gas, log_byte on the 5 decoded bytes"
    (cost o "read_memory_base" == price "read_memory_base" &&
      cost o "read_memory_byte" == 10 * price "read_memory_byte" &&
      cost o "utf16_decoding_base" == price "utf16_decoding_base" &&
      cost o "utf16_decoding_byte" == 10 * price "utf16_decoding_byte" &&
      cost o "log_base" == price "log_base" && cost o "log_byte" == 5 * price "log_byte")
  let o := exec (← log16 (units [0x20AC]) [2, 0])
  check "log_utf16: a three-byte character, log_byte on the 3 decoded bytes"
    (o.logs == ["€"] && cost o "utf16_decoding_byte" == 2 * price "utf16_decoding_byte" &&
      cost o "log_byte" == 3 * price "log_byte")
  let o := exec (← log16 (units [0x61, 0xD83D, 0xDE00]) [6, 0])
  check "log_utf16: a surrogate pair is one four-byte character"
    (o.logs == ["a😀"] && cost o "utf16_decoding_byte" == 6 * price "utf16_decoding_byte" &&
      cost o "log_byte" == 5 * price "log_byte")
  let o := exec (← log16 hello [9, 0])
  check "log_utf16: an odd length is BadUTF16 after the read, before any decoding byte"
    (failsWith o .badUTF16 && o.logs == [] &&
      cost o "read_memory_byte" == 9 * price "read_memory_byte" &&
      cost o "utf16_decoding_base" == price "utf16_decoding_base" &&
      cost o "utf16_decoding_byte" == 0 && cost o "log_base" == 0)
  let o := exec (← log16 (units [0x61, 0xD83D, 0x62]) [6, 0])
  check "log_utf16: an unpaired surrogate is BadUTF16 after the decoding bytes, before log_base"
    (failsWith o .badUTF16 && o.logs == [] &&
      cost o "utf16_decoding_byte" == 6 * price "utf16_decoding_byte" && cost o "log_base" == 0)
  let o := exec (← log16 (units [0xDE00]) [2, 0])
  check "log_utf16: a lone low surrogate is BadUTF16" (failsWith o .badUTF16)
  let o := exec (← log16 hello [10, 1099511627776])
  check "log_utf16: out of bounds is a memory access violation after the read is paid"
    (failsWith o .memoryAccessViolation &&
      cost o "read_memory_byte" == 10 * price "read_memory_byte" &&
      cost o "utf16_decoding_byte" == 0)
  -- the NUL-terminated form
  let o := exec (← log16 (units [0x68, 0x69, 0] ++ [7]) [-1, 0])
  check "log_utf16: u64::MAX reads up to a NUL code unit"
    (o.logs == ["hi"] && cost o "read_memory_base" == 3 * price "read_memory_base" &&
      cost o "read_memory_byte" == 6 * price "read_memory_byte" &&
      cost o "utf16_decoding_byte" == 4 * price "utf16_decoding_byte" &&
      cost o "log_byte" == 2 * price "log_byte")
  let o := exec (← log16 (units [0x68, 0x69, 0]) [-1, 1099511627776])
  check "log_utf16: the NUL-terminated scan stops at the end of memory"
    (failsWith o .memoryAccessViolation)
  let o := exec (← log16 (units [0x68, 0x69, 0x6A, 0]) [-1, 0]) (limited 4 100)
  check "log_utf16: the NUL-terminated scan stops at the remaining log length"
    (failsWith o (.totalLogLengthExceeded 6 4) && cost o "read_memory_base" == 3 * price "read_memory_base" &&
      cost o "utf16_decoding_byte" == 0)
  -- log lengths count the decoded message
  let o := exec (← log16 (units [0x20AC, 0x20AC]) [4, 0]) (limited 5 100)
  check "log_utf16: the total log length counts decoded bytes (4 raw fit, 6 decoded do not)"
    (failsWith o (.totalLogLengthExceeded 12 5) && o.logs == [] &&
      cost o "log_byte" == 6 * price "log_byte")
  let o := exec (← log16 hello [10, 0]) (limited 4 100)
  check "log_utf16: a raw length above the remaining log length is rejected before decoding"
    (failsWith o (.totalLogLengthExceeded 10 4) && cost o "utf16_decoding_byte" == 0)
  let o := exec (← log16 hello [10, 0]) (limited 100 0)
  check "log_utf16: too many logs is rejected after the base cost only"
    (failsWith o (.numberOfLogsExceeded 0) && cost o "base" == price "base" &&
      cost o "utf16_decoding_base" == 0 && cost o "read_memory_base" == 0)
  -- log_utf8
  let o := exec (← log8 (bytesOf "héllo") [6, 0])
  check "log_utf8: valid UTF-8 is stored; log_byte counts the bytes"
    (o.logs == ["héllo"] && cost o "utf8_decoding_byte" == 6 * price "utf8_decoding_byte" &&
      cost o "log_byte" == 6 * price "log_byte")
  let o := exec (← log8 [0x61, 0xFF, 0x62] [3, 0])
  check "log_utf8: invalid UTF-8 is BadUTF8 after the decoding bytes, before log_base"
    (failsWith o .badUTF8 && o.logs == [] &&
      cost o "utf8_decoding_byte" == 3 * price "utf8_decoding_byte" && cost o "log_base" == 0)
  let o := exec (← log8 [0xED, 0xA0, 0x80] [3, 0])
  check "log_utf8: an encoded surrogate is BadUTF8" (failsWith o .badUTF8)
  let o := exec (← log8 [0xC0, 0x80] [2, 0])
  check "log_utf8: an overlong encoding is BadUTF8" (failsWith o .badUTF8)
  let o := exec (← log8 [0xF4, 0x90, 0x80, 0x80] [4, 0])
  check "log_utf8: a code point above U+10FFFF is BadUTF8" (failsWith o .badUTF8)
  let o := exec (← log8 [0xE2, 0x82] [2, 0])
  check "log_utf8: a truncated sequence is BadUTF8" (failsWith o .badUTF8)
  let o := exec (← log8 (bytesOf "abc" ++ [0, 9]) [-1, 0])
  check "log_utf8: u64::MAX reads up to a NUL byte, one read per byte"
    (o.logs == ["abc"] && cost o "read_memory_base" == 4 * price "read_memory_base" &&
      cost o "read_memory_byte" == 4 * price "read_memory_byte" &&
      cost o "utf8_decoding_byte" == 3 * price "utf8_decoding_byte" &&
      cost o "log_byte" == 3 * price "log_byte")
  let o := exec (← log8 (bytesOf "abcd" ++ [0]) [-1, 0]) (limited 3 100)
  check "log_utf8: the NUL-terminated scan stops at the remaining log length"
    (failsWith o (.totalLogLengthExceeded 4 3) && cost o "read_memory_base" == 4 * price "read_memory_base" &&
      cost o "utf8_decoding_byte" == 0)
  let o := exec (← log8 (bytesOf "abcd") [4, 0]) (limited 3 100)
  check "log_utf8: a length above the remaining log length is rejected before the read"
    (failsWith o (.totalLogLengthExceeded 4 3) && cost o "read_memory_base" == 0 &&
      cost o "utf8_decoding_base" == price "utf8_decoding_base")
  let o := exec (← log8 (bytesOf "abcd") [4, 1099511627776])
  check "log_utf8: out of bounds is a memory access violation after the read is paid"
    (failsWith o .memoryAccessViolation && cost o "read_memory_byte" == 4 * price "read_memory_byte")
  -- panic_utf8
  let o := exec (← build "panic_utf8" false (bytesOf "boom") [4, 0])
  check "panic_utf8: the message is the panic"
    (o.aborted == some (.hostError (.guestPanic "boom")) &&
      cost o "utf8_decoding_byte" == 4 * price "utf8_decoding_byte" && cost o "log_base" == 0)
  let o := exec (← build "panic_utf8" false [0xFF] [1, 0])
  check "panic_utf8: invalid UTF-8 is BadUTF8" (failsWith o .badUTF8)
  let o := exec (← build "panic_utf8" false (bytesOf "boom" ++ [0]) [-1, 0])
  check "panic_utf8: u64::MAX reads up to a NUL byte"
    (o.aborted == some (.hostError (.guestPanic "boom")) &&
      cost o "read_memory_base" == 5 * price "read_memory_base")
  -- abort(msg_ptr, filename_ptr, line, col): two length-prefixed UTF-16 strings
  let mem := u32le 4 ++ units [0x68, 0x69] ++ u32le 2 ++ units [0x66]
  let o := exec (← build "abort" true mem [4, 12, 7, 9])
  let message := "hi, filename: \"f\" line: 7 col: 9"
  check "abort: logs ABORT: and panics with the message"
    (o.aborted == some (.hostError (.guestPanic message)) && o.logs == ["ABORT: " ++ message])
  check "abort: gas of the two lengths, two strings, and the message"
    (cost o "read_memory_base" == 4 * price "read_memory_base" &&
      cost o "read_memory_byte" == 14 * price "read_memory_byte" &&
      cost o "utf16_decoding_base" == 2 * price "utf16_decoding_base" &&
      cost o "utf16_decoding_byte" == 6 * price "utf16_decoding_byte" &&
      cost o "log_byte" == message.utf8ByteSize * price "log_byte")
  let o := exec (← build "abort" true mem [3, 12, 7, 9])
  check "abort: a pointer below 4 is BadUTF16 after the base cost"
    (failsWith o .badUTF16 && o.logs == [] && cost o "read_memory_base" == 0)
  let o := exec (← build "abort" true (u32le 3 ++ units [0x68]) [4, 12, 7, 9])
  check "abort: an odd message length is BadUTF16" (failsWith o .badUTF16 && o.logs == [])

end LogHosts
