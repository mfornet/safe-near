import NearVM.CryptoHost
import NearVM.Utf

/-!
# Reading strings for `log_utf8`, `log_utf16`, `panic_utf8` and `abort`

`near_vm_runner::logic::VMLogic::{log_utf8, log_utf16, panic_utf8, abort}` with their helpers
`get_utf8_string`, `get_utf16_string`, `get_nul_terminated_utf16_len`, `checked_push_log` and
`check_can_add_a_log_message`. As for the cryptographic hosts (`NearVM.CryptoHost`), one function
returns everything the call decides, so that the order of charges, reads and errors is written
once:

* `charges`: what is paid before the call ends (`ExtCosts` names and counts, in order);
* `result`: the message as UTF-8 bytes, or the error that ends the call after those charges.

`Metered.chargesBefore` reads the charges, `Metered.preInvokeError` the error, and the host
functions (`Host.logUtf8Fn`, `Host.logUtf16Fn`, `Metered.panicUtf8Metered`,
`Metered.abortMetered`) the message.

Memory is read exactly as nearcore does: never through a register (`len = u64::MAX` selects the
NUL-terminated form, not a register), a range read pays `read_memory_base` and
`read_memory_byte * len` before the bounds check, and a NUL-terminated string is read one byte
(`log_utf8`, `panic_utf8`) or one `u16` (`log_utf16`) at a time, each read paying its own
`read_memory_*`.

nearcore divergence: an address `ptr + i` of the NUL-terminated `get_utf8_string` loop is not
wrapped modulo `2^64`; it is out of bounds.
-/

namespace Wasm.Near

def leBytesToNat : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leBytesToNat bs

/-- What one string-reading host call pays and returns. -/
structure StringRead where
  charges : List (String × Nat)
  result : Except HostError (List UInt8)

/-- Bytes of guest memory. -/
def memorySize (st : HostStore NearState) : Nat := st.mem.size * 65536

/-- `total_log_length`: the bytes of the messages logged so far. -/
def totalLogLength (st : HostStore NearState) : Nat := (st.host.logs.map List.length).sum

private def u64Cap (n : Nat) : Nat := min n (2 ^ 64 - 1)

/-- `max_total_log_length - total_log_length` (saturating); unbounded without a configured limit. -/
def logSpace (st : HostStore NearState) : Nat :=
  match st.host.config.maxLogLen with
  | none => 2 ^ 64 - 1
  | some limit => limit - totalLogLength st

/-- `total_log_length_exceeded(add_len)`. -/
def totalLogLengthExceeded (st : HostStore NearState) (addLen : Nat) : HostError :=
  .totalLogLengthExceeded (u64Cap (totalLogLength st + addLen))
    (st.host.config.maxLogLen.getD (2 ^ 64 - 1))

/-- `check_can_add_a_log_message`. -/
def logCountError (st : HostStore NearState) : Option HostError :=
  match st.host.config.maxNumberLogs with
  | some limit => if st.host.logs.length ≥ limit then some (.numberOfLogsExceeded limit) else none
  | none => none

private def baseCharge : List (String × Nat) := [ext1 "base"]

/-- `Memory::view`: the base cost, then the per-byte cost (`IntegerOverflow` when the product
does not fit a `u64`, after the base cost was paid). -/
private def viewCharges (st : HostStore NearState) (len : Nat) :
    List (String × Nat) × Option HostError :=
  if payPerOverflows st "read_memory_byte" len then
    ([ext1 "read_memory_base"], some .integerOverflow)
  else ([ext1 "read_memory_base", ext1 "read_memory_byte" len], none)

/-- `get_u8` / `get_u16` / `get_u32`, `reads` times. -/
private def smallReads (reads size : Nat) : List (String × Nat) :=
  (List.replicate reads [ext1 "read_memory_base", ext1 "read_memory_byte" size]).flatten

/-- The loop of the NUL-terminated `get_utf8_string`: the number of `get_u8` calls and the bytes
before the NUL, or the error. `maxLen` bounds the string; reading `maxLen + 1` bytes without a NUL
exceeds the log length. -/
def scanNulBytes (st : HostStore NearState) (ptr maxLen : Nat) :
    Nat → Nat → List UInt8 → Nat × Except HostError (List UInt8)
  | 0, i, acc => (i, .ok acc.reverse)
  | fuel + 1, i, acc =>
    if ptr + i + 1 > memorySize st then (i + 1, .error .memoryAccessViolation)
    else
      let el := st.mem.read8 (ptr + i)
      if el == 0 then (i + 1, .ok acc.reverse)
      else if i == maxLen then (i + 1, .error (totalLogLengthExceeded st (maxLen + 1)))
      else scanNulBytes st ptr maxLen fuel (i + 1) (el :: acc)

/-- `get_nul_terminated_utf16_len`: the byte length before the first `0x00 0x00` code unit, with
the length at which the scan stopped (each step reads one `u16`). -/
def scanNulUnits (st : HostStore NearState) (ptr maxLen : Nat) :
    Nat → Nat → Nat × Except HostError Nat
  | 0, len => (len, .ok len)
  | fuel + 1, len =>
    if ptr + len + 2 > memorySize st then (len, .error .memoryAccessViolation)
    else if st.mem.read8 (ptr + len) == 0 && st.mem.read8 (ptr + len + 1) == 0 then (len, .ok len)
    else if len + 2 ≤ maxLen then scanNulUnits st ptr maxLen fuel (len + 2)
    else (len, .error (totalLogLengthExceeded st (len + 2)))

/-- `get_utf8_string(len, ptr)`, after the caller paid for the call. -/
def readUtf8String (st : HostStore NearState) (len ptr : UInt64) : StringRead :=
  let head := [ext1 "utf8_decoding_base"]
  let maxLen := logSpace st
  let finish (acc : List (String × Nat)) (buf : List UInt8) : StringRead :=
    let acc := acc ++ [ext1 "utf8_decoding_byte" buf.length]
    if validUtf8 buf then ⟨acc, .ok buf⟩ else ⟨acc, .error .badUTF8⟩
  if len != u64Max then
    if len.toNat > maxLen then ⟨head, .error (totalLogLengthExceeded st len.toNat)⟩
    else
      let (view, overflow) := viewCharges st len.toNat
      let acc := head ++ view
      if let some e := overflow then ⟨acc, .error e⟩
      else if ptr.toNat + len.toNat > memorySize st then ⟨acc, .error .memoryAccessViolation⟩
      else finish acc (st.mem.readList ptr.toNat len.toNat)
  else
    let (reads, scanned) := scanNulBytes st ptr.toNat maxLen (maxLen + 1) 0 []
    let acc := head ++ smallReads reads 1
    match scanned with
    | .error e => ⟨acc, .error e⟩
    | .ok buf => finish acc buf

/-- A complete fixed-length UTF-8 read contract, including the exact charge
plan. Clients can project either the decoded bytes or the cost without
unfolding the private memory-view helper. -/
theorem readUtf8String_fixed (st : HostStore NearState) (len ptr : UInt64)
    (bytes : List UInt8) (hlen : len ≠ u64Max)
    (hspace : len.toNat ≤ logSpace st)
    (hcost : st.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hbound : ptr.toNat + len.toNat ≤ memorySize st)
    (hbytes : st.mem.readList ptr.toNat len.toNat = bytes)
    (hutf : validUtf8 bytes = true) :
    readUtf8String st len ptr =
      ⟨[ext1 "utf8_decoding_base", ext1 "read_memory_base",
        ext1 "read_memory_byte" len.toNat, ext1 "utf8_decoding_byte" bytes.length], .ok bytes⟩ := by
  simp [readUtf8String, hlen, Nat.not_lt_of_ge hspace, viewCharges,
    payPerOverflows, Nat.not_le_of_lt hcost, Nat.not_lt_of_ge hbound, hbytes, hutf]

/-- The decoded-result projection of the complete fixed-length contract. -/
theorem readUtf8String_fixed_ok (st : HostStore NearState) (len ptr : UInt64)
    (bytes : List UInt8) (hlen : len ≠ u64Max)
    (hspace : len.toNat ≤ logSpace st)
    (hcost : st.host.extCosts.cost "read_memory_byte" * len.toNat < 2 ^ 64)
    (hbound : ptr.toNat + len.toNat ≤ memorySize st)
    (hbytes : st.mem.readList ptr.toNat len.toNat = bytes)
    (hutf : validUtf8 bytes = true) :
    (readUtf8String st len ptr).result = .ok bytes :=
  congrArg StringRead.result
    (readUtf8String_fixed st len ptr bytes hlen hspace hcost hbound hbytes hutf)

/-- `get_utf16_string(len, ptr)`, after the caller paid for the call: UTF-16LE to UTF-8. -/
def readUtf16String (st : HostStore NearState) (len ptr : UInt64) : StringRead :=
  let head := [ext1 "utf16_decoding_base"]
  let maxLen := logSpace st
  let decode (acc : List (String × Nat)) (n : Nat) (buf : List UInt8) : StringRead :=
    match utf16Units buf with
    | none => ⟨acc, .error .badUTF16⟩
    | some units =>
      if n > maxLen then ⟨acc, .error (totalLogLengthExceeded st n)⟩
      else
        let acc := acc ++ [ext1 "utf16_decoding_byte" n]
        match decodeUtf16Units units with
        | some out => ⟨acc, .ok out⟩
        | none => ⟨acc, .error .badUTF16⟩
  if len != u64Max then
    let (view, overflow) := viewCharges st len.toNat
    let acc := head ++ view
    if let some e := overflow then ⟨acc, .error e⟩
    else if ptr.toNat + len.toNat > memorySize st then ⟨acc, .error .memoryAccessViolation⟩
    else decode acc len.toNat (st.mem.readList ptr.toNat len.toNat)
  else
    let (stop, scanned) := scanNulUnits st ptr.toNat maxLen (maxLen / 2 + 2) 0
    let acc := head ++ smallReads (stop / 2 + 1) 2
    match scanned with
    | .error e => ⟨acc, .error e⟩
    | .ok n => decode acc n (st.mem.readList ptr.toNat n)

/-- `log_base`, `log_byte * msg.len()`, then `checked_push_log` of `pushLen` bytes. A rejected push
has already counted the message, so its length is added twice. -/
def finishLog (st : HostStore NearState) (acc : List (String × Nat)) (msg : List UInt8)
    (pushLen : Nat) : StringRead :=
  let acc := acc ++ [ext1 "log_base", ext1 "log_byte" msg.length]
  match st.host.config.maxLogLen with
  | some limit =>
    if totalLogLength st + pushLen > limit then
      ⟨acc, .error (totalLogLengthExceeded st (2 * pushLen))⟩
    else ⟨acc, .ok msg⟩
  | none => ⟨acc, .ok msg⟩

/-- `log_utf8(len, ptr)`. -/
def logUtf8Read (st : HostStore NearState) (len ptr : UInt64) : StringRead :=
  match logCountError st with
  | some e => ⟨baseCharge, .error e⟩
  | none =>
    let r := readUtf8String st len ptr
    match r.result with
    | .error e => ⟨baseCharge ++ r.charges, .error e⟩
    | .ok msg => finishLog st (baseCharge ++ r.charges) msg msg.length

/-- `log_utf16(len, ptr)`: the message is the decoded UTF-8; `log_byte` and the log length count it. -/
def logUtf16Read (st : HostStore NearState) (len ptr : UInt64) : StringRead :=
  match logCountError st with
  | some e => ⟨baseCharge, .error e⟩
  | none =>
    let r := readUtf16String st len ptr
    match r.result with
    | .error e => ⟨baseCharge ++ r.charges, .error e⟩
    | .ok msg => finishLog st (baseCharge ++ r.charges) msg msg.length

/-- `panic_utf8(len, ptr)`: the panic message. -/
def panicUtf8Read (st : HostStore NearState) (len ptr : UInt64) : StringRead :=
  let r := readUtf8String st len ptr
  ⟨baseCharge ++ r.charges, r.result⟩

/-- `"ABORT: "`, which prefixes the logged message. -/
def abortLogPrefix : List UInt8 := "ABORT: ".toUTF8.toList

/-- `abort(msg_ptr, filename_ptr, line, col)`: the panic message; the log entry is
`abortLogPrefix ++ message`. The pointers address UTF-16 strings preceded by their byte length. -/
def abortRead (st : HostStore NearState) (msgPtr filePtr line col : UInt32) : StringRead :=
  if msgPtr < 4 || filePtr < 4 then ⟨baseCharge, .error .badUTF16⟩
  else match logCountError st with
  | some e => ⟨baseCharge, .error e⟩
  | none =>
    let lenAt (ptr : UInt32) : Option Nat :=
      if ptr.toNat - 4 + 4 > memorySize st then none
      else some (leBytesToNat (st.mem.readList (ptr.toNat - 4) 4))
    let acc1 := baseCharge ++ smallReads 1 4
    match lenAt msgPtr with
    | none => ⟨acc1, .error .memoryAccessViolation⟩
    | some msgLen =>
      let acc2 := acc1 ++ smallReads 1 4
      match lenAt filePtr with
      | none => ⟨acc2, .error .memoryAccessViolation⟩
      | some fileLen =>
        let msg := readUtf16String st (UInt64.ofNat msgLen) msgPtr.toUInt64
        match msg.result with
        | .error e => ⟨acc2 ++ msg.charges, .error e⟩
        | .ok msgBytes =>
          let file := readUtf16String st (UInt64.ofNat fileLen) filePtr.toUInt64
          match file.result with
          | .error e => ⟨acc2 ++ msg.charges ++ file.charges, .error e⟩
          | .ok fileBytes =>
            let message := msgBytes ++ ", filename: \"".toUTF8.toList ++ fileBytes ++
              "\" line: ".toUTF8.toList ++ (toString line.toNat).toUTF8.toList ++
              " col: ".toUTF8.toList ++ (toString col.toNat).toUTF8.toList
            finishLog st (acc2 ++ msg.charges ++ file.charges) message
              (abortLogPrefix.length + message.length)

/-- The string-reading call `name` makes with `args`, if it is one. -/
def stringHostRead? (name : String) (st : HostStore NearState) (args : List Value) :
    Option StringRead :=
  let a := argU64 args
  let a32 (i : Nat) : UInt32 :=
    match args[i]? with
    | some (.i32 n) => n
    | _ => 0
  match name with
  | "log_utf8" => some (logUtf8Read st (a 0) (a 1))
  | "log_utf16" => some (logUtf16Read st (a 0) (a 1))
  | "panic_utf8" => some (panicUtf8Read st (a 0) (a 1))
  | "abort" => some (abortRead st (a32 0) (a32 1) (a32 2) (a32 3))
  | _ => none

end Wasm.Near
