#!/usr/bin/env python3
"""Fill contract.wasm, hash.txt and deployment block info for a dataset entry.

usage: fetch_binary.py contracts/<name> [--no-deploy-block]

Reads contract.toml, fetches the code of the first mainnet deployment, checks
that its hash equals contract.toml code_hash, writes contract.wasm and hash.txt and
records verified_block_* (and deploy_block_* unless --no-deploy-block) for
every deployment in contract.toml.
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import near_rpc as nr
import contract_toml


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    want_deploy = "--no-deploy-block" not in sys.argv
    d = args[0].rstrip("/")
    mpath = os.path.join(d, "contract.toml")
    m = contract_toml.load(mpath)
    expected = m["code_hash"]
    deployments = [x for x in m.get("deployments", []) if x.get("network", "mainnet") == "mainnet"]
    if not deployments:
        print(f"{d}: no mainnet deployment in contract.toml, nothing fetched", file=sys.stderr)
        return 1
    for dep in deployments:
        acc = dep["account_id"]
        wasm, res = nr.view_code(acc)
        h = nr.code_hash(wasm)
        if h != expected:
            print(f"{d}: {acc} has code_hash {h}, contract.toml says {expected}", file=sys.stderr)
            return 1
        dep["verified_block_height"] = res["block_height"]
        dep["verified_block_hash"] = res["block_hash"]
        if want_deploy and "deploy_block_height" not in dep:
            b = nr.find_deploy_block(acc, expected, hi=res["block_height"])
            dep["deploy_block_height"] = b
            dep["deploy_block_hash"] = nr.view_account(acc, b, archival=True)["block_hash"]
            dep["code_hash_before"] = nr.code_hash_at(acc, b - 1)
        wasm_path = os.path.join(d, "contract.wasm")
        open(wasm_path, "wb").write(wasm)
        open(os.path.join(d, "hash.txt"), "w").write(expected + "\n")
        print(f"{d}: {acc} ok, {len(wasm)} bytes, hash {expected}, deploy block {dep.get('deploy_block_height')}")
    contract_toml.dump(m, mpath)
    return 0


if __name__ == "__main__":
    sys.exit(main())
