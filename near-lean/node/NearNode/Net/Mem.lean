import NearNode.Net

/-!
# In-memory network

`Hub.net` is a `Net` whose connections never leave the process: `listen` registers an address with
the hub and `connect` hands the listener one end of a pair of buffers. It does what the sockets do
that the node depends on (data in order, end of file after `close`, timeouts, a refused connection
to an address nobody listens on) and nothing else, so that protocol tests are fast and deterministic.
-/

namespace Near.Node.Net.Mem

/-- One direction of a connection. -/
structure Pipe where
  data : IO.Ref ByteArray
  /-- Set when the writer closed; the reader still gets what was written. -/
  closed : IO.Ref Bool

private def Pipe.new : IO Pipe := do
  pure { data := ← IO.mkRef ByteArray.empty, closed := ← IO.mkRef false }

/-- Takes up to `max` bytes, polling until `timeoutMs` has passed. -/
private partial def Pipe.take (p : Pipe) (max timeoutMs : Nat) :
    IO (Except Closed (Option ByteArray)) := do
  let started ← IO.monoMsNow
  let rec loop : IO (Except Closed (Option ByteArray)) := do
    let d ← p.data.get
    if d.size > 0 then
      let n := Nat.min max d.size
      p.data.set (d.extract n d.size)
      return .ok (some (d.extract 0 n))
    if ← p.closed.get then
      return .error .eof
    if (← IO.monoMsNow) - started ≥ timeoutMs then
      return .ok none
    IO.sleep 1
    loop
  loop

/-- One end of a connection. -/
def endpoint (inbox outbox : Pipe) (peer : Addr) : Stream where
  read max timeoutMs := inbox.take max timeoutMs
  write bytes _ := do
    if ← outbox.closed.get then
      throw (IO.userError "broken pipe")
    outbox.data.modify (· ++ bytes)
  close := outbox.closed.set true
  peer

/-- A connection that is waiting to be accepted. -/
private structure Pending where
  stream : Stream

/-- Waits for the first pending connection of a listener, polling until `timeoutMs` has passed. -/
private partial def acceptLoop (queue : IO.Ref (Array Pending)) (timeoutMs started : Nat) :
    IO (Option Stream) := do
  let q ← queue.get
  if let some p := q[0]? then
    queue.set (q.extract 1 q.size)
    return some p.stream
  if (← IO.monoMsNow) - started ≥ timeoutMs then
    return none
  IO.sleep 1
  acceptLoop queue timeoutMs started

/-- The addresses that are listened on. -/
structure Hub where
  listeners : IO.Ref (List (Addr × IO.Ref (Array Pending)))
  /-- The port given to the next connecting end. -/
  nextPort : IO.Ref UInt16

namespace Hub

def new : IO Hub := do
  pure { listeners := ← IO.mkRef [], nextPort := ← IO.mkRef 50000 }

/-- The `Net` of this hub. -/
def net (h : Hub) : Net where
  connect addr _ := do
    let some (_, queue) := (← h.listeners.get).find? (·.1 == addr)
      | throw (IO.userError s!"connection refused: {addr}")
    let port ← h.nextPort.modifyGet fun p => (p, p + 1)
    let client : Addr := ⟨ByteArray.mk #[127, 0, 0, 1], port⟩
    let up ← Pipe.new
    let down ← Pipe.new
    queue.modify (·.push ⟨endpoint up down client⟩)
    pure (endpoint down up addr)
  listen addr := do
    if (← h.listeners.get).any (·.1 == addr) then
      throw (IO.userError s!"address in use: {addr}")
    let queue ← IO.mkRef #[]
    h.listeners.modify ((addr, queue) :: ·)
    pure {
          addr
          accept := fun timeoutMs => do
            acceptLoop queue timeoutMs (← IO.monoMsNow)
          close := h.listeners.modify (·.filter (·.1 != addr)) }

end Hub

end Near.Node.Net.Mem
