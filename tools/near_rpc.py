#!/usr/bin/env python3
"""Minimal NEAR RPC helpers for the contracts dataset (stdlib only).

Commands:
  near_rpc.py account <account_id> [--block H]      -> view_account JSON
  near_rpc.py code <account_id> <out.wasm> [--block H]
                                                    -> write code, print base58 sha256
  near_rpc.py hash <file.wasm>                       -> base58 sha256 (NEAR code_hash)
  near_rpc.py metadata <account_id>                  -> NEP-330 contract_source_metadata
  near_rpc.py view <account_id> <method> [json_args] -> call view method
  near_rpc.py deploy-block <account_id> [--hash H]   -> first block of the latest run of
                                                        blocks whose code_hash == H
"""
import argparse, base64, hashlib, json, sys, time, urllib.request

RPC = "https://rpc.mainnet.fastnear.com"
ARCHIVAL_RPC = "https://archival-rpc.mainnet.fastnear.com"
MAINNET_GENESIS_HEIGHT = 9820210
REQUEST_DELAY = 0.6  # seconds between archival requests, to stay under public rate limits
B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58encode(b: bytes) -> str:
    n = int.from_bytes(b, "big")
    s = ""
    while n:
        n, r = divmod(n, 58)
        s = B58[r] + s
    return "1" * (len(b) - len(b.lstrip(b"\0"))) + s


def code_hash(wasm: bytes) -> str:
    return b58encode(hashlib.sha256(wasm).digest())


def rpc(method, params, url=RPC, retries=8):
    body = json.dumps({"jsonrpc": "2.0", "id": "safe-near", "method": method, "params": params}).encode()
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, body, {"Content-Type": "application/json"})
            with urllib.request.urlopen(req, timeout=60) as r:
                d = json.load(r)
            if "error" in d:
                err = d["error"]
                name = (err.get("cause") or {}).get("name", "")
                if name in ("UNKNOWN_BLOCK", "GARBAGE_COLLECTED_BLOCK", "UNKNOWN_ACCOUNT", "NO_CONTRACT_CODE"):
                    raise LookupError(name)
                raise RuntimeError(json.dumps(err)[:500])
            return d["result"]
        except urllib.error.HTTPError as e:
            if e.code == 422:  # block height outside of the known range (e.g. below genesis)
                raise LookupError("UNKNOWN_BLOCK")
            if e.code == 429 and attempt < retries - 1:
                time.sleep(5.0 * (attempt + 1))
                continue
            raise
        except (urllib.error.URLError, TimeoutError):
            if attempt == retries - 1:
                raise
            time.sleep(1.5 * (attempt + 1))


def block_ref(block):
    return {"block_id": block} if block is not None else {"finality": "final"}


def view_account(account, block=None, archival=False):
    return rpc("query", {"request_type": "view_account", "account_id": account, **block_ref(block)},
               url=ARCHIVAL_RPC if archival or block is not None else RPC)


def view_code(account, block=None):
    res = rpc("query", {"request_type": "view_code", "account_id": account, **block_ref(block)},
              url=ARCHIVAL_RPC if block is not None else RPC)
    return base64.b64decode(res["code_base64"]), res


def call_view(account, method, args=None, block=None):
    args_b64 = base64.b64encode(json.dumps(args or {}).encode()).decode()
    res = rpc("query", {"request_type": "call_function", "account_id": account, "method_name": method,
                        "args_base64": args_b64, **block_ref(block)},
              url=ARCHIVAL_RPC if block is not None else RPC)
    if res.get("error"):
        raise RuntimeError(res["error"])
    raw = bytes(res["result"])
    try:
        return json.loads(raw)
    except ValueError:
        return raw.decode(errors="replace")


def code_hash_at(account, block):
    """code_hash of account at block, or None if the account did not exist / block unknown."""
    for delta in range(0, 50):  # skip over missing block heights
        time.sleep(REQUEST_DELAY)
        try:
            return view_account(account, block + delta, archival=True)["code_hash"]
        except LookupError as e:
            if str(e) == "UNKNOWN_BLOCK":
                continue
            return None
    raise RuntimeError(f"no block found near {block}")


def find_deploy_block(account, target_hash, hi=None):
    """Binary search for the start of the most recent run of blocks with code_hash == target_hash.

    Assumes the hash is set at `hi` (latest) and searches for the smallest block height b such
    that code_hash(b') == target_hash for all probed b' in [b, hi]. The result is the block that
    includes the DeployContract receipt (the first block at which the new code is visible).
    """
    if hi is None:
        acc = view_account(account)
        hi = acc["block_height"]
        assert acc["code_hash"] == target_hash, f"account hash {acc['code_hash']} != {target_hash}"
    lo = MAINNET_GENESIS_HEIGHT
    while lo < hi:
        mid = (lo + hi) // 2
        h = code_hash_at(account, mid)
        if h == target_hash:
            hi = mid
        else:
            lo = mid + 1
    return lo


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("account"); p.add_argument("account"); p.add_argument("--block", type=int)
    p = sub.add_parser("code"); p.add_argument("account"); p.add_argument("out"); p.add_argument("--block", type=int)
    p = sub.add_parser("hash"); p.add_argument("file")
    p = sub.add_parser("metadata"); p.add_argument("account")
    p = sub.add_parser("view"); p.add_argument("account"); p.add_argument("method"); p.add_argument("args", nargs="?", default="{}")
    p = sub.add_parser("deploy-block"); p.add_argument("account"); p.add_argument("--hash")
    a = ap.parse_args()

    if a.cmd == "account":
        print(json.dumps(view_account(a.account, a.block), indent=2))
    elif a.cmd == "code":
        wasm, res = view_code(a.account, a.block)
        open(a.out, "wb").write(wasm)
        h = code_hash(wasm)
        assert h == res["hash"], (h, res["hash"])
        print(json.dumps({"account_id": a.account, "block_height": res["block_height"],
                          "block_hash": res["block_hash"], "code_hash": h, "size": len(wasm)}))
    elif a.cmd == "hash":
        print(code_hash(open(a.file, "rb").read()))
    elif a.cmd == "metadata":
        print(json.dumps(call_view(a.account, "contract_source_metadata"), indent=2))
    elif a.cmd == "view":
        print(json.dumps(call_view(a.account, a.method, json.loads(a.args)), indent=2))
    elif a.cmd == "deploy-block":
        h = a.hash or view_account(a.account)["code_hash"]
        b = find_deploy_block(a.account, h)
        print(json.dumps({"account_id": a.account, "code_hash": h, "deploy_block_height": b,
                          "code_hash_before": code_hash_at(a.account, b - 1)}))


if __name__ == "__main__":
    main()
