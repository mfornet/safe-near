import Std.Internal.UV.TCP
import Std.Net
import NearNode.Net

/-!
# TCP on Lean's libuv binding

The only module of the node that uses `Std.Internal`. Lean's runtime owns the event loop and the
sockets; this file only turns its promises into the blocking calls with timeouts of `NearNode.Net`.

A receive of libuv cannot be given up without risk (`cancelRecv` is documented as dangerous), so each
connection has a reader task that receives for as long as the connection lives and appends what
arrives to a buffer, and `read` takes from that buffer, waiting for it in small steps. A socket is
closed by the runtime when the last reference to it goes, so `close` stops the reader and shuts the
write side down.
-/

namespace Near.Node.Net.Uv

open Std.Internal.UV.TCP Std.Net

/-- A socket address of Lean's `Std.Net`. -/
def toSocketAddress (a : Addr) : Except String SocketAddress :=
  if a.ip.size == 4 then .ok (.v4 ⟨IPv4Addr.ofParts a.ip[0]! a.ip[1]! a.ip[2]! a.ip[3]!, a.port⟩)
  else .error "only IPv4 addresses are supported"

def ofSocketAddress : SocketAddress → Addr
  | .v4 a => ⟨ByteArray.mk a.addr.octets.toArray, a.port⟩
  | .v6 a =>
    ⟨ByteArray.mk
        (a.addr.segments.toArray.flatMap fun (s : UInt16) => #[(s >>> 8).toUInt8, s.toUInt8]),
      a.port⟩

/-- The receive side of a connection, shared with its reader task. -/
private structure Inbox where
  data : IO.Ref ByteArray
  /-- Why no more data will come, once that is known. -/
  ended : IO.Ref (Option Closed)
  /-- Whether `close` was called. -/
  stopped : IO.Ref Bool

/-- Receives until the connection ends or `close` was called. -/
private partial def readerLoop (sock : Socket) (inbox : Inbox) : IO Unit := do
  if ← inbox.stopped.get then
    inbox.ended.modify fun e => e.orElse fun _ => some .eof
    return
  let promise ← sock.recv? 65536
  match ← IO.wait promise.result? with
  | some (.ok (some b)) =>
    inbox.data.modify (· ++ b)
    readerLoop sock inbox
  | some (.ok none) | none =>
    inbox.ended.set (some .eof)
  | some (.error e) =>
    inbox.ended.set (some (.error (toString e)))

/-- Waits for a promise for at most `timeoutMs`; `none` if it is not resolved by then. -/
private partial def awaitLoop (p : IO.Promise (Except IO.Error α)) (timeoutMs started : Nat)
    (delay : UInt32) : IO (Option α) := do
  if ← p.isResolved then
    match ← IO.wait p.result? with
    | some (.ok a) =>
      return some a
    | some (.error e) =>
      throw e
    | none =>
      throw (IO.userError "promise dropped")
  if (← IO.monoMsNow) - started ≥ timeoutMs then
    return none
  IO.sleep delay
  awaitLoop p timeoutMs started (if delay < 8 then delay * 2 else delay)

private def awaitPromise (p : IO.Promise (Except IO.Error α)) (timeoutMs : Nat) : IO (Option α) :=
  do
  awaitLoop p timeoutMs (← IO.monoMsNow) 1

/-- Accepts from a listening socket, polling until `timeoutMs` has passed. -/
private partial def acceptLoop (server : Socket) (timeoutMs started : Nat) (delay : UInt32)
    (wrap : Socket → IO Stream) : IO (Option Stream) := do
  match ← IO.ofExcept (← server.tryAccept) with
  | some sock =>
    return some (← wrap sock)
  | none =>
    if (← IO.monoMsNow) - started ≥ timeoutMs then
      return none
    IO.sleep delay
    acceptLoop server timeoutMs started (if delay < 8 then delay * 2 else delay) wrap

/-- Takes from the inbox, polling until `timeoutMs` has passed. -/
private partial def takeLoop (inbox : Inbox) (max timeoutMs started : Nat) (delay : UInt32) :
    IO (Except Closed (Option ByteArray)) := do
  let taken ←
    inbox.data.modifyGet fun d =>
        if d.size > 0 then
          let n := Nat.min max d.size
          (some (d.extract 0 n), d.extract n d.size)
        else (none, d)
  if let some b := taken then
    return .ok (some b)
  if let some why← inbox.ended.get then
    -- the reader may have appended just before it ended
    if (← inbox.data.get).size == 0 then
      return .error why
    return ← takeLoop inbox max timeoutMs started 0
  if (← IO.monoMsNow) - started ≥ timeoutMs then
    return .ok none
  IO.sleep delay
  takeLoop inbox max timeoutMs started (if delay < 4 then delay * 2 else delay)

/-- A connected socket as a `Stream`. -/
private def stream (sock : Socket) (peer : Addr) : IO Stream := do
  let inbox : Inbox :=
    { data := ← IO.mkRef ByteArray.empty, ended := ← IO.mkRef none, stopped := ← IO.mkRef false }
  discard <| IO.asTask (readerLoop sock inbox) Task.Priority.dedicated
  pure {
        peer
        read := fun max timeoutMs => do
          takeLoop inbox max timeoutMs (← IO.monoMsNow) 1
        write := fun bytes timeoutMs => do
          if let some why← inbox.ended.get then
            throw (IO.userError s!"connection closed: {repr why}")
          let promise ← sock.send #[bytes]
          match ← awaitPromise promise timeoutMs with
          | some _ =>
            pure ()
          | none =>
            throw (IO.userError "write timed out")
        close := do
          inbox.stopped.set true
          try
            discard <| sock.shutdown
          catch _ =>
            pure ()
          sock.cancelRecv }

/-- TCP on libuv. -/
def net : Net where
  connect addr timeoutMs := do
    let target ← IO.ofExcept (toSocketAddress addr |>.mapError IO.userError)
    let sock ← Socket.new
    let promise ← sock.connect target
    match ← awaitPromise promise timeoutMs with
    | some _ =>
      sock.noDelay
      stream sock addr
    | none =>
      throw (IO.userError s!"connect to {addr} timed out")
  listen addr := do
    let target ← IO.ofExcept (toSocketAddress addr |>.mapError IO.userError)
    let server ← Socket.new
    server.bind target
    server.listen 128
    let local_ ← server.getSockName
    pure {
          addr := ofSocketAddress local_
          accept := fun timeoutMs => do
            acceptLoop server timeoutMs (← IO.monoMsNow) 1 fun sock => do
                sock.noDelay
                let peer ← sock.getPeerName
                stream sock (ofSocketAddress peer)
          close := pure () }

end Near.Node.Net.Uv
