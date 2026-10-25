/-!
# Network transport

The node talks to its peers through three small interfaces and nothing else: a byte `Stream`, a
`Listener` and a `Net` that connects and listens. `NearNode.Net.Uv` implements them on Lean's own
libuv binding (`Std.Internal.UV.TCP`, an internal API of Lean, which is why it sits behind this
interface) and `NearNode.Net.Mem` in memory, for tests that need no sockets. Nothing else of the
node imports `Std.Internal`.

`Framed` is the framing of `chain/network/src/peer/stream.rs`: every message is a `u32` little-endian
length and then that many bytes; a longer message than 512 MiB closes the connection. Reads and
writes take a timeout in milliseconds, as nearcore's `READ_TIMEOUT` and `WRITE_TIMEOUT` (two
minutes) do.
-/

namespace Near.Node.Net

/-- An IP address and a port: 4 or 16 octets. -/
structure Addr where
  ip : ByteArray
  port : UInt16
  deriving BEq, Inhabited

namespace Addr

/-- `a.b.c.d:port`. -/
def parse? (s : String) : Option Addr :=
  match s.splitOn ":" with
  | [host, port] =>
    match host.splitOn ".", port.toNat? with
    | [a, b, c, d], some p =>
      match a.toNat?, b.toNat?, c.toNat?, d.toNat? with
      | some a, some b, some c, some d =>
        if a < 256 && b < 256 && c < 256 && d < 256 && p < 65536 then
          some ⟨ByteArray.mk #[a.toUInt8, b.toUInt8, c.toUInt8, d.toUInt8], p.toUInt16⟩
        else none
      | _, _, _, _ => none
    | _, _ => none
  | _ => none

instance : ToString Addr :=
  ⟨fun a =>
    if a.ip.size == 4 then s!"{a.ip[0]!}.{a.ip[1]!}.{a.ip[2]!}.{a.ip[3]!}:{a.port}"
    else s!"[{a.ip.size} octets]:{a.port}"⟩

end Addr

/-- Why a read returned no data. -/
inductive Closed where
  /-- The peer closed the connection. -/
  | eof
  /-- The connection failed. -/
  | error (msg : String)
  deriving BEq, Inhabited, Repr

/-- A connected byte stream. -/
structure Stream where
  /-- Reads what is available, at most `max` bytes, waiting at most `timeoutMs`: `ok none` when
  nothing arrived in time, `ok (some bytes)` otherwise (never empty). A closed or failed stream is
  `error`. -/
  read : (max : Nat) → (timeoutMs : Nat) → IO (Except Closed (Option ByteArray))
  /-- Writes everything, waiting at most `timeoutMs` for the peer to take it. -/
  write : ByteArray → (timeoutMs : Nat) → IO Unit
  /-- Closes the stream; the peer reads end of file after what was written. -/
  close : IO Unit
  /-- The address of the peer. -/
  peer : Addr

/-- A bound socket that accepts connections. -/
structure Listener where
  /-- Waits at most `timeoutMs` for a connection. -/
  accept : (timeoutMs : Nat) → IO (Option Stream)
  close : IO Unit
  /-- The bound address (with the port the system chose, for port 0). -/
  addr : Addr

/-- Connects and listens. -/
structure Net where
  /-- Connects to `addr`, waiting at most `timeoutMs`; throws if it cannot. -/
  connect : Addr → (timeoutMs : Nat) → IO Stream
  listen : Addr → IO Listener

/-- nearcore's `NETWORK_MESSAGE_MAX_SIZE_BYTES`. -/
def maxFrameBytes : Nat :=
  512 * 1048576

/-- nearcore's `READ_TIMEOUT` and `WRITE_TIMEOUT`, in milliseconds. -/
def ioTimeoutMs : Nat :=
  120000

/-- What `Framed.recv` returns. -/
inductive Frame where
  | message (bytes : ByteArray)
  | timeout
  | closed (why : Closed)
  /-- The length prefix announces more than `maxFrameBytes`. -/
  | tooLarge (length : Nat)
  deriving Inhabited

/-- A stream with the framing of nearcore. -/
structure Framed where
  stream : Stream
  /-- Bytes read and not yet consumed. -/
  pending : IO.Ref ByteArray
  maxFrame : Nat := maxFrameBytes

namespace Framed

def new (s : Stream) (maxFrame : Nat := maxFrameBytes) : IO Framed := do
  pure { stream := s, pending := ← IO.mkRef ByteArray.empty, maxFrame }

/-- Writes one message: the length as `u32` little-endian, then the message, in one write. -/
def send (f : Framed) (msg : ByteArray) (timeoutMs : Nat := ioTimeoutMs) : IO Unit := do
  if msg.size > f.maxFrame then
    throw (IO.userError s!"message of {msg.size} bytes is larger than the limit {f.maxFrame}")
  let n := msg.size
  let prefix_ :=
    ByteArray.mk #[n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]
  f.stream.write (prefix_ ++ msg) timeoutMs

/-- The first complete message of `buf`, and the rest. -/
private def split (buf : ByteArray) (max : Nat) : Except Nat (Option (ByteArray × ByteArray)) :=
  if buf.size < 4 then .ok none
  else
    let n :=
      buf[0]!.toNat ||| (buf[1]!.toNat <<< 8) ||| (buf[2]!.toNat <<< 16) ||| (buf[3]!.toNat <<< 24)
    if n > max then .error n
    else
      if buf.size < 4 + n then .ok none
      else .ok (some (buf.extract 4 (4 + n), buf.extract (4 + n) buf.size))

/-- Reads one message, waiting at most `timeoutMs` for it to be complete; what was read of an
incomplete message stays for the next call. -/
partial def recv (f : Framed) (timeoutMs : Nat) : IO Frame := do
  let started ← IO.monoMsNow
  let rec loop : IO Frame := do
    let buf ← f.pending.get
    match split buf f.maxFrame with
    | .error n =>
      return .tooLarge n
    | .ok (some (msg, rest)) =>
      f.pending.set rest
      return .message msg
    | .ok none =>
      let elapsed := (← IO.monoMsNow) - started
      if elapsed ≥ timeoutMs && timeoutMs > 0 then
        return .timeout
      let want :=
        if buf.size ≥ 4 then
          let n :=
            buf[0]!.toNat ||| (buf[1]!.toNat <<< 8) ||| (buf[2]!.toNat <<< 16) |||
              (buf[3]!.toNat <<< 24)
          max 4096 (min (4 + n - buf.size) 1048576)
        else 4096
      match ← f.stream.read want (timeoutMs - elapsed) with
      | .error why =>
        return .closed why
      | .ok none =>
        if timeoutMs == 0 then
          return .timeout
        else
          loop
      | .ok (some bytes) =>
        f.pending.set (buf ++ bytes)
        loop
  loop

def close (f : Framed) : IO Unit :=
  f.stream.close

end Framed

end Near.Node.Net
