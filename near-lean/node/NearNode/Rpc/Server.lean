import NearNode.Rpc.Http
import NearNode.Rpc.Validators
import NearNode.Net.Uv

/-!
# The JSON-RPC server

`chain/jsonrpc/src/lib.rs`: the HTTP routes of the node (`POST /` for JSON-RPC requests, `GET /status`,
`GET /health`, `GET /network_info`, CORS preflight), the JSON-RPC envelope and the dispatch on the method name.

* A request is a JSON object with `jsonrpc: "2.0"`, a `method`, `params` (missing is `null`) and an `id`; anything
  else, a batch included, is a `PARSE_ERROR` ("JSON RPC Request format was expected", status 400).
* A result is `{"jsonrpc":"2.0","result":...,"id":...}`; an error carries the `RpcError` object and the HTTP status of
  `rpc_handler`.
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Net Near.Node.Network Near.Node.Validator

structure Server where
  ctx : Ctx
  /-- Whether the connection to the peer is up. -/
  connected : IO.Ref Bool
  peerAddr : String
  peerId : PublicKey

private def corsHeaders : List (String × String) :=
  [("vary", "origin, access-control-request-method, access-control-request-headers"),
    ("access-control-allow-origin", "*")]

private def jsonResponse (status : Nat) (body : Json) : Response :=
  { status, headers := [("content-type", "application/json")] ++ corsHeaders,
    body := body.compress.toUTF8 }

def networkInfo (srv : Server) : IO R := do
  let up ← srv.connected.get
  let s ← srv.ctx.env.get
  let peers : Array Json :=
    if up then
      #[Json.mkObj [("id", jkey srv.peerId), ("addr", srv.peerAddr), ("account_id", Json.null)]]
    else #[]
  let epoch := (s.st.block s.tip).toOption.bind fun t => (s.st.epoch t.view.epochId).toOption
  let producers : Array Json :=
    match epoch with
    | some e =>
      (e.info.view.validators.filter fun v => v.accountId != srv.ctx.env.me).map fun v =>
        Json.mkObj
          [("account_id", jacc v.accountId), ("addr", Json.null), ("peer_id", jkey srv.peerId)]
    | none => #[]
  return .ok
      (Json.mkObj
        [("active_peers", Json.arr peers), ("num_active_peers", jn peers.size),
          ("peer_max_count", jn 40), ("sent_bytes_per_sec", jn 0), ("received_bytes_per_sec", jn 0),
          ("known_producers", Json.arr producers)])

def dispatch (srv : Server) (method : String) (params : Json) : IO R := do
  let c := srv.ctx
  match method with
  | "status" =>
    return .ok (← status c)
  | "health" =>
    return .ok Json.null
  | "network_info" =>
    networkInfo srv
  | "gas_price" =>
    gasPrice c params
  | "block" =>
    block c params
  | "chunk" =>
    chunk c params
  | "query" =>
    query c params
  | "tx" =>
    txStatusRequest c params false
  | "EXPERIMENTAL_tx_status" =>
    txStatusRequest c params true
  | "send_tx" =>
    sendTxRequest c params false
  | "broadcast_tx_commit" =>
    sendTxRequest c params true
  | "broadcast_tx_async" =>
    broadcastAsync c params
  | "validators" =>
    validators c params
  | "EXPERIMENTAL_genesis_config" | "genesis_config" =>
    return .ok (genesisConfig c)
  | "EXPERIMENTAL_changes_in_block" | "block_effects" =>
    changesInBlock c params
  | "EXPERIMENTAL_protocol_config" =>
    protocolConfig c params
  | _ =>
    return .error (RpcError.methodNotFound method)

/-- The response of one JSON-RPC request. -/
def handleMessage (srv : Server) (msg : Json) : IO Response := do
  let nullId := Json.null
  let fail (e : RpcError) (id : Json) : Response :=
    jsonResponse e.status (Json.mkObj [("jsonrpc", "2.0"), ("error", e.error), ("id", id)])
  match msg with
  | .obj _ =>
    let id := (field? msg "id").getD Json.null
    match field? msg "jsonrpc", field? msg "method" with
    | some (.str "2.0"), some (.str method) =>
      let params := (field? msg "params").getD Json.null
      match ← dispatch srv method params with
      | .ok result =>
        return jsonResponse 200 (Json.mkObj [("jsonrpc", "2.0"), ("result", result), ("id", id)])
      | .error e =>
        return fail e id
    | _, _ =>
      return fail (RpcError.parse "JSON RPC Request format was expected") nullId
  | _ =>
    return fail (RpcError.parse "JSON RPC Request format was expected") nullId

def handle (srv : Server) (req : Request) : IO Response := do
  let preflight : Response :=
    { status := 200,
      headers := [("allow", "POST"), ("access-control-allow-methods", "*")] ++ corsHeaders }
  match req.method, req.path with
  | "OPTIONS", _ =>
    return preflight
  | "GET", "/status" =>
    return jsonResponse 200 (← status srv.ctx)
  | "GET", "/health" =>
    return jsonResponse 200 Json.null
  | "GET", "/network_info" =>
    match ← networkInfo srv with
    | .ok j =>
      return jsonResponse 200 j
    | .error _ =>
      return { status := 503, headers := corsHeaders }
  | "POST", "/" =>
    match String.fromUTF8? req.body with
    | none =>
      return { status := 400,
               headers := [("content-type", "text/plain; charset=utf-8")] ++ corsHeaders,
               body := "Failed to parse the request body as JSON: invalid UTF-8".toUTF8 }
    | some text =>
      match Json.parse text with
      | .error e =>
        return { status := 400,
                 headers := [("content-type", "text/plain; charset=utf-8")] ++ corsHeaders,
                 body := s!"Failed to parse the request body as JSON: {e}".toUTF8 }
      | .ok msg =>
        handleMessage srv msg
  | "GET", "/" | "PUT", "/" | "DELETE", "/" | "HEAD", "/" =>
    return { status := 405, headers := [("allow", "POST")] ++ corsHeaders }
  | _, _ =>
    return { status := 404, headers := corsHeaders }

/-- Listens on `addr` and serves until `stop` is set. -/
def run (srv : Server) (addr : Addr) (stop : IO.Ref Bool) : IO Unit := do
  let listener ← Uv.net.listen addr
  serve listener stop (handle srv)

end Near.Node.Rpc
