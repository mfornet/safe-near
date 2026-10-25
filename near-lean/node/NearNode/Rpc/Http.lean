import NearNode.Net

/-!
# HTTP/1.1

The part of HTTP a JSON-RPC server needs, over `NearNode.Net` (so over libuv in the node and over memory
in tests): requests with `Content-Length` or chunked bodies, keep-alive connections, and responses with
a length. The limits follow the server of nearcore (`axum`): a header block of at most 64 KiB, a body of
at most `json_payload_max_size` (10 MiB, `413` above), and an idle connection is closed after 30 s.
-/

namespace Near.Node.Rpc

open Near.Node.Net

structure Request where
  method : String
  path : String
  /-- Header names in lower case. -/
  headers : List (String × String)
  body : ByteArray

def Request.header? (r : Request) (name : String) : Option String :=
  (r.headers.find? (·.1 == name)).map (·.2)

structure Response where
  status : Nat
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty

def reason : Nat → String
  | 200 => "OK"
  | 400 => "Bad Request"
  | 404 => "Not Found"
  | 405 => "Method Not Allowed"
  | 408 => "Request Timeout"
  | 413 => "Payload Too Large"
  | 422 => "Unprocessable Entity"
  | 500 => "Internal Server Error"
  | 503 => "Service Unavailable"
  | _ => "Status"

/-- The bytes of a response; `close` adds `connection: close`. -/
def Response.encode (r : Response) (close : Bool := false) : ByteArray :=
  let head :=
    s!"HTTP/1.1 {r.status} {reason r.status}\r\n" ++
      String.join (r.headers.map fun (k, v) => s!"{k}: {v}\r\n") ++
      s!"content-length: {r.body.size}\r\n" ++
      (if close then "connection: close\r\n" else "") ++
      "\r\n"
  head.toUTF8 ++ r.body

/-- The index of the first `\r\n\r\n` in `b`. -/
private def headerEnd (b : ByteArray) : Option Nat :=
  Id.run do
    if b.size < 4 then
      return none
    for i in [0:b.size - 3] do
      if b[i]! == 13 && b[i + 1]! == 10 && b[i + 2]! == 13 && b[i + 3]! == 10 then
        return some i
    return none

private def lower (s : String) : String :=
  s.map Char.toLower

/-- Parses the request line and the headers. -/
private def parseHead (text : String) :
    Option (String × String × String × List (String × String)) := do
  let lines := text.splitOn "\r\n"
  let first :: rest := lines | none
  let [m, p, v] := first.splitOn " " | none
  let mut hs : List (String × String) := []
  for l in rest do
    match l.splitOn ":" with
    | name :: value =>
      hs := hs ++ [(lower name.trimAscii.toString, (":".intercalate value).trimAscii.toString)]
    | [] =>
      none
  pure (m, p, v, hs)

/-- Why a request could not be read. -/
inductive ReadError where
  | closed
  | timeout
  | tooLarge
  | bad (why : String)
  deriving Repr

/-- State of a connection: the bytes read and not consumed. -/
structure Conn where
  stream : Stream
  pending : IO.Ref ByteArray

def Conn.new (s : Stream) : IO Conn :=
  return { stream := s, pending := ← IO.mkRef ByteArray.empty }

/-- Reads more bytes into `pending`; `false` when the connection ended or nothing came in `timeoutMs`. -/
private def fill (c : Conn) (timeoutMs : Nat) : IO (Except ReadError Unit) := do
  match ← c.stream.read 65536 timeoutMs with
  | .error _ =>
    return .error .closed
  | .ok none =>
    return .error .timeout
  | .ok (some b) =>
    c.pending.modify (· ++ b)
    return .ok ()

private def takeBytes (c : Conn) (n : Nat) (timeoutMs : Nat) : IO (Except ReadError ByteArray) := do
  let started ← IO.monoMsNow
  repeat
    let b ← c.pending.get
    if b.size ≥ n then
      c.pending.set (b.extract n b.size)
      return .ok (b.extract 0 n)
    let left := timeoutMs - min timeoutMs ((← IO.monoMsNow) - started)
    match ← fill c left with
    | .error e =>
      return .error e
    | .ok () =>
      pure ()
  return .error .closed

/-- The first `\r\n` terminated line of `pending`, read from the stream if needed. -/
private def takeLine (c : Conn) (timeoutMs : Nat) : IO (Except ReadError String) := do
  let started ← IO.monoMsNow
  repeat
    let b ← c.pending.get
    for i in [0:b.size] do
      if b[i]! == 10 then
        c.pending.set (b.extract (i + 1) b.size)
        let line := String.fromUTF8! (b.extract 0 i)
        return .ok (line.dropEndWhile (· == '\r')).toString
    if b.size > 65536 then
      return .error .tooLarge
    let left := timeoutMs - min timeoutMs ((← IO.monoMsNow) - started)
    match ← fill c left with
    | .error e =>
      return .error e
    | .ok () =>
      pure ()
  return .error .closed

/-- Reads one request. `idleMs` bounds the wait for its first byte. -/
partial def readRequest (c : Conn) (idleMs : Nat := 30000) (maxBody : Nat := 10 * 1048576) :
    IO (Except ReadError Request) := do
  let started ← IO.monoMsNow
  -- the head
  let mut head : Option Nat := none
  repeat
    let b ← c.pending.get
    head := headerEnd b
    if head.isSome then
      break
    if b.size > 65536 then
      return .error .tooLarge
    let left := idleMs - min idleMs ((← IO.monoMsNow) - started)
    if left == 0 then
      return .error .timeout
    match ← fill c left with
    | .error e =>
      return .error e
    | .ok () =>
      pure ()
  let some end_ := head | return .error .closed
  let b ← c.pending.get
  let headText := String.fromUTF8! (b.extract 0 end_)
  c.pending.set (b.extract (end_ + 4) b.size)
  let some (m, p, _, hs) := parseHead headText | return .error (.bad "request line")
  let req : Request := { method := m, path := p, headers := hs, body := ByteArray.empty }
  let transfer := (req.header? "transfer-encoding").map lower
  if transfer.any (·.contains "chunked") then
    let mut body := ByteArray.empty
    repeat
      match ← takeLine c 30000 with
      | .error e =>
        return .error e
      | .ok line =>
        let hex := (line.splitOn ";").head!.trimAscii.toString
        let size :=
          hex.foldl
            (fun n ch =>
              n * 16 +
                (if ch.isDigit then ch.toNat - 48
                else if 'a' ≤ ch.toLower && ch.toLower ≤ 'f' then ch.toLower.toNat - 87 else 0))
            0
        if size == 0 then
          -- trailers up to the empty line
          repeat
            match ← takeLine c 30000 with
            | .error e =>
              return .error e
            | .ok l =>
              if l.isEmpty then
                break
          return .ok { req with body }
        if body.size + size > maxBody then
          return .error .tooLarge
        match ← takeBytes c size 30000 with
        | .error e =>
          return .error e
        | .ok chunk =>
          body := body ++ chunk
        match ← takeLine c 30000 with
        | .error e =>
          return .error e
        | .ok _ =>
          pure ()
    return .error .closed
  else
    let len := ((req.header? "content-length").bind String.toNat?).getD 0
    if len > maxBody then
      return .error .tooLarge
    match ← takeBytes c len 30000 with
    | .error e =>
      return .error e
    | .ok body =>
      return .ok { req with body }

/-- Serves the connections of `listener` until `stop` is set: every connection in a task of its own,
every request answered by `handle`. -/
partial def serve (listener : Listener) (stop : IO.Ref Bool) (handle : Request → IO Response) :
    IO Unit := do
  let rec loop : IO Unit := do
    if ← stop.get then
      listener.close
      return
    match ← listener.accept 200 with
    | none =>
      loop
    | some stream =>
      discard <| IO.asTask (serveConnection stream) Task.Priority.dedicated
      loop
  loop
where serveConnection (stream : Stream) : IO Unit := do
    try
      let conn ← Conn.new stream
      let mut go := true
      while go do
        if ← stop.get then
          break
        match ← readRequest conn with
        | .error .timeout | .error .closed =>
          go := false
        | .error .tooLarge =>
          stream.write (Response.encode { status := 413 } true) 10000
          go := false
        | .error (.bad _) =>
          stream.write (Response.encode { status := 400 } true) 10000
          go := false
        | .ok req =>
          let close := (req.header? "connection").any (lower · == "close")
          let resp ←
            try
              handle req
            catch e =>
              pure { status := 500, body := s!"{e}".toUTF8 }
          stream.write (resp.encode close) 30000
          if close then
            go := false
    catch _ =>
      pure ()
    stream.close

end Near.Node.Rpc
