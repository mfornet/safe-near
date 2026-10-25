import NearNode.Net.Uv
import NearNode.Network

open Near.Node Near.Node.Net Near.Node.Network

def main (args : List String) : IO UInt32 := do
  if args == ["genkey"] then
    let seed ← IO.getRandomBytes 32
    let some k := NodeKey.ofSeed? seed | return 1
    IO.eprintln s!"\{\"account_id\":\"node\",\"public_key\":\"{k.peerId.key.toText}\",\"secret_key\":\"ed25519:{base58Encode (seed ++ k.signing.publicKey)}\"}"
    return 0
  let [peerText, keyFile, chainId, genesisB58, secs] := args | IO.eprintln "usage"; return 2
  let some (pk, addrText) := (peerText.splitOn "@") |>.toArray |> fun a => if a.size == 2 then some (a[0]!, a[1]!) else none | IO.eprintln "peer"; return 2
  let some peerKey := PublicKey.parse? pk | IO.eprintln "peer key"; return 2
  let some addr := Addr.parse? addrText | IO.eprintln "addr"; return 2
  let keyJson ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile keyFile))
  let some key := NodeKey.ofJson? keyJson | IO.eprintln "key"; return 2
  let some gh := base58Decode? genesisB58 | IO.eprintln "genesis"; return 2
  let cfg : Config := { key, genesisId := ⟨chainId, ⟨gh⟩⟩, listenPort := some 24999 }
  let s ← Uv.net.connect addr 5000
  match ← handshakeOutbound cfg systemClock s ⟨peerKey⟩ .t2 none 0 with
  | .error e => IO.eprintln s!"handshake failed: {e.describe}"; return 1
  | .ok l =>
    IO.eprintln s!"handshake ok: peer height {l.theirs.senderChainInfo.height}, version {l.protocolVersion}, edge nonce {l.edge.nonce}"
    let started ← IO.monoMsNow
    while (← IO.monoMsNow) - started < secs.toNat! * 1000 do
      match ← l.recv 1000 with
      | .message m n => IO.eprintln s!"message {n} bytes: {repr (m.encode.size)} {match m with | .syncRoutingTable u => s!"routing table {u.edges.size} edges {u.accounts.size} accounts" | .block b => "block" | .peersRequest _ => "peers request" | .blockHeaders h => s!"headers {h.size}" | .syncAccountsData _ => "accounts data" | .syncSnapshotHosts _ => "snapshot hosts" | _ => "other"}"
      | .timeout => pure ()
      | .closed w => IO.eprintln s!"closed: {w}"; return 1
      | .undecodable n => IO.eprintln s!"undecodable {n}"
      | .oversized n => IO.eprintln s!"oversized {n}"
    return 0
