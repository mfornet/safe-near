import NearNode.Net.Mem
import NearNode.Net.Uv

/-!
`node-net-tests`: the framing, the in-memory network and the libuv TCP transport behind the same
interface. Every check runs on both transports.
-/

open Near.Node.Net

private initialize checks : IO.Ref Nat ←
  IO.mkRef 0

private def check (failures : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  checks.modify (· + 1)
  if !ok then
    IO.eprintln s!"FAIL {name}"
    failures.modify (· + 1)

private def bytesOf (n : Nat) (seed : Nat) : ByteArray :=
  ByteArray.mk ((Array.range n).map fun i => ((i * 31 + seed) % 251).toUInt8)

/-- Both ends of a connection on `net`, listening at `addr`. -/
private def pair (net : Net) (addr : Addr) : IO (Framed × Framed × Listener) := do
  let l ← net.listen addr
  let client ← net.connect l.addr 2000
  let some server ← l.accept 2000 | throw (IO.userError "no connection accepted")
  pure (← Framed.new client, ← Framed.new server, l)

private def frameEq (f : Frame) (b : ByteArray) : Bool :=
  match f with
  | .message m => m == b
  | _ => false

private def exercise (failures : IO.Ref Nat) (label : String) (net : Net)
    (addr second unused : Addr) : IO Unit := do
  let (client, server, listener) ← pair net addr
  -- one message each way, and an empty one
  client.send (bytesOf 10 1)
  check failures s!"{label}: client to server" (frameEq (← server.recv 2000) (bytesOf 10 1))
  server.send (bytesOf 0 2)
  check failures s!"{label}: empty message" (frameEq (← client.recv 2000) (bytesOf 0 2))
  -- nothing to read: a timeout, and the connection stays usable
  match ← server.recv 50 with
  | .timeout =>
    pure ()
  | _ =>
    check failures s!"{label}: timeout" false
  -- messages in a burst arrive in order
  for i in [0:50] do
    client.send (bytesOf (i * 7) i)
  let mut inOrder := true
  for i in [0:50] do
    inOrder := inOrder && frameEq (← server.recv 2000) (bytesOf (i * 7) i)
  check failures s!"{label}: order" inOrder
  -- a message larger than one read
  let big := bytesOf 3000000 5
  client.send big
  check failures s!"{label}: large message" (frameEq (← server.recv 20000) big)
  -- a message that arrives in pieces: a prefix and a part of the body, then the rest
  let raw := bytesOf 100 9
  let prefix_ := ByteArray.mk #[100, 0, 0, 0]
  client.stream.write (prefix_ ++ raw.extract 0 30) 2000
  match ← server.recv 50 with
  | .timeout =>
    pure ()
  | _ =>
    check failures s!"{label}: partial message is not a message" false
  client.stream.write (raw.extract 30 100) 2000
  check failures s!"{label}: completed message" (frameEq (← server.recv 2000) raw)
  -- a length above the limit
  let small ← Framed.new server.stream 16
  client.stream.write (ByteArray.mk #[17, 0, 0, 0] ++ bytesOf 17 3) 2000
  match ← small.recv 2000 with
  | .tooLarge 17 =>
    pure ()
  | _ =>
    check failures s!"{label}: too large" false
  -- the sender closes: what was written is read, then the end of the file
  let (c2, s2, _) ← pair net second
  c2.send (bytesOf 5 6)
  c2.close
  check failures s!"{label}: data before close" (frameEq (← s2.recv 2000) (bytesOf 5 6))
  match ← s2.recv 2000 with
  | .closed .eof =>
    pure ()
  | _ =>
    check failures s!"{label}: end of file" false
  client.close
  server.close
  listener.close
  -- nobody listens
  let refused ←
    try
      discard <| net.connect unused 500
      pure false
    catch _ =>
      pure true
  check failures s!"{label}: connection refused" refused

def main (_ : List String) : IO UInt32 := do
  let failures ← IO.mkRef 0
  let hub ← Mem.Hub.new
  exercise failures "memory" hub.net ⟨ByteArray.mk #[10, 0, 0, 1], 4000⟩
      ⟨ByteArray.mk #[10, 0, 0, 1], 4001⟩ ⟨ByteArray.mk #[10, 0, 0, 2], 4000⟩
  exercise failures "tcp" Uv.net ⟨ByteArray.mk #[127, 0, 0, 1], 0⟩ ⟨ByteArray.mk #[127, 0, 0, 1], 0⟩
      ⟨ByteArray.mk #[127, 0, 0, 1], 1⟩
  let n ← failures.get
  IO.println s!"net tests: {← checks.get} checks, {n} failures"
  return if n == 0 then 0 else 1
