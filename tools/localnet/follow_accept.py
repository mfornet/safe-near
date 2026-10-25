#!/usr/bin/env python3
"""Acceptance of the syncing observer (M7): the Lean node state-syncs a running `neard` localnet and follows it.

``just localnet-follow`` runs this.  For each topology it

1. starts the pinned `neard` localnet and runs a workload on it (the scenarios of ``workload.py``; with
   ``--full-workload`` including the heavy ones: host function calls, the 14 calls of 300 Tgas, the wait for a yield
   to time out), then keeps light traffic going (``workload.py --steady``) for the rest of the run;
2. starts ``near-lean-node peer --sync-mode state`` from the genesis files only: it checks the headers from the
   genesis to the head, asks the localnet for the state of the shards at the block `neard` serves for the current
   epoch (header, parts, over the peer-to-peer network), checks them, builds the tries, and applies the blocks from there;
3. follows the head for ``--follow`` seconds, while this script samples `neard`'s head over RPC every second; with
   ``--lightburst`` a burst of heavy calls is sent a minute after the node reached the head, to see how far it falls
   behind and how fast it catches up.

Checks: the state sync completed with nothing refused; the node was within ``--max-lag`` blocks of `neard`'s head
within ``--reach-limit`` seconds of starting; it stayed within that many blocks for the whole follow window (a
window with a burst: it caught up again within ``--catch-up-limit`` seconds); no disconnect, no failure; every
chunk's `ChunkExtra` and outgoing receipts equal to what the next chunk carries; and for every block it applied,
the state root of each shard equal to ``prev_state_root`` of the next block's chunk as `neard` returns it over RPC.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import statistics
import subprocess
import sys
import tempfile
import threading
import time

import chain_corpus
import localnet
import peer_accept

ROOT = chain_corpus.ROOT
BINARY = ROOT / "near-lean/node/.lake/build/bin/near-lean-node"
HERE = Path(__file__).resolve().parent


class Sampler(threading.Thread):
    """`neard`'s head height over RPC, once a second."""

    def __init__(self, topology: str):
        super().__init__(daemon=True)
        self.topology = topology
        self.samples: list[tuple[float, int]] = []
        self.stopped = threading.Event()

    def run(self) -> None:
        while not self.stopped.is_set():
            try:
                height = localnet.rpc(self.topology, "status", [], timeout=3)["result"]["sync_info"]["latest_block_height"]
                self.samples.append((time.time(), height))
            except Exception:
                pass
            self.stopped.wait(1.0)


def head_at(samples: list[tuple[float, int]], t: float) -> int | None:
    """The head at time `t`: the last sample not after it."""
    best = None
    for when, height in samples:
        if when <= t:
            best = height
        else:
            break
    return best


def lag_series(node_rows: list[dict], samples: list[tuple[float, int]]) -> list[tuple[float, int, int]]:
    """(time, head, lag) for each line of the node's lag log: neard's head minus the node's applied height."""
    out = []
    for row in node_rows:
        t = row["unixMs"] / 1000
        head = head_at(samples, t)
        if head is not None:
            # until the first block is applied the node has not caught up with anything
            if row.get("blocks", 1) > 0:
                out.append((t, head, max(0, head - row["applied"])))
    return out


def analyse(series: list[tuple[float, int, int]], started: float, max_lag: int, burst_at: float | None) -> dict:
    """The numbers the report gives, from the lag series."""
    result: dict = {"samples": len(series)}
    reached = next((t for t, _, lag in series if lag <= max_lag), None)
    result["reachedAfterSeconds"] = None if reached is None else round(reached - started, 1)
    if reached is None:
        return result
    after = [(t, head, lag) for t, head, lag in series if t >= reached]
    lags = [lag for _, _, lag in after]
    result.update(maxLagAfterReach=max(lags), medianLag=statistics.median(lags), meanLag=round(sum(lags) / len(lags), 2),
                  secondsAboveLimit=sum(1 for lag in lags if lag > max_lag), followedSeconds=round(after[-1][0] - reached, 1))
    if burst_at is not None:
        during = [(t, lag) for t, _, lag in after if t >= burst_at]
        peak = max((lag for _, lag in during), default=0)
        peak_time = next((t for t, lag in during if lag == peak), burst_at)
        back = next((t for t, lag in during if t > peak_time and lag <= max_lag), None)
        result.update(burstPeakLag=peak, burstPeakAfterSeconds=round(peak_time - burst_at, 1),
                      burstCaughtUpAfterSeconds=None if back is None else round(back - burst_at, 1))
    return result


def run_workload(topology: str, extra: list[str], log: Path, timeout: float) -> int:
    process = subprocess.Popen([sys.executable, str(HERE / "workload.py"), topology] + extra,
                               stdout=log.open("w"), stderr=subprocess.STDOUT, cwd=HERE)
    try:
        return process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        return -1


def accept(topology: str, options: argparse.Namespace) -> bool:
    localnet.stop(topology)
    localnet.init(topology)
    localnet.start(topology)
    node_dir = localnet.home(topology) / "node0"
    boot_key = json.loads((node_dir / "node_key.json").read_text())["public_key"]
    port = localnet.network_port(topology, 0)
    sampler = Sampler(topology)
    background: list[subprocess.Popen] = []
    node = None
    result = False
    try:
        localnet.wait_ready(topology)
        genesis_hash = peer_accept.rpc(topology, "status", [])["genesis_hash"]
        with tempfile.TemporaryDirectory(prefix="safe-near-follow-") as temporary:
            work = Path(temporary)
            if options.keep:
                work = Path(options.keep) / topology
                work.mkdir(parents=True, exist_ok=True)
            peer_accept.bootstrap(topology, work, genesis_hash)
            sampler.start()
            # 1. the workload that builds the history the node syncs past
            started_workload = time.time()
            skip = [] if options.full_workload else peer_accept.HEAVY
            code = run_workload(topology, ["--skip"] + skip, work / "workload.log", options.workload_limit)
            head = peer_accept.rpc(topology, "status", [])["sync_info"]["latest_block_height"]
            print(f"{topology}: workload ended with {code} after {time.time() - started_workload:.0f} s, head {head}",
                  flush=True)
            if code != 0:
                print((work / "workload.log").read_text()[-2000:])
                return False
            # 2. light traffic for the rest of the run
            steady_log = (work / "steady.log").open("w")
            steady = subprocess.Popen(
                [sys.executable, str(HERE / "workload.py"), topology, "--no-scenarios", "--steady",
                 str(options.follow + options.reach_limit + 600), "--period", str(options.period)],
                stdout=steady_log, stderr=subprocess.STDOUT, cwd=HERE)
            background.append(steady)
            time.sleep(options.settle)
            # 3. the node
            report, applied, lag_log = work / "report.json", work / "applied.jsonl", work / "lag.jsonl"
            command = [str(options.binary), "peer", "--chain-dir", str(work), "--node-key", str(work / "node_key.json"),
                       "--boot", f"{boot_key}@127.0.0.1:{port}", "--listen", str(port + 100),
                       "--sync-mode", "state", "--follow", str(options.follow), "--seconds",
                       str(options.follow + options.reach_limit + 900), "--reach-lag", str(options.max_lag),
                       "--applied-log", str(applied), "--report", str(report), "--lag-log", str(lag_log),
                       "--configs", str(ROOT / "near-lean/vm/configs"), "--profile"]
            if options.track:
                command += ["--track-shards", options.track]
            node_started = time.time()
            node = subprocess.Popen(command, stdout=subprocess.DEVNULL, stderr=(work / "node.log").open("w"))
            listed = False
            burst_at = None
            reached_seen = None
            while node.poll() is None:
                try:
                    key_file = work / "node_key.json"
                    if key_file.exists() and not listed:
                        node_id = json.loads(key_file.read_text())["public_key"]
                        listed = any(p["id"] == node_id for p in peer_accept.rpc(topology, "network_info", [])["active_peers"])
                except Exception:
                    pass
                if options.lightburst and burst_at is None and lag_log.exists():
                    rows = [json.loads(line) for line in lag_log.read_text().splitlines() if line.strip()]
                    series = lag_series(rows, sampler.samples)
                    if reached_seen is None:
                        reached_seen = next((t for t, _, lag in series if lag <= options.max_lag), None)
                    elif time.time() - reached_seen > options.burst_delay:
                        burst_at = time.time()
                        print(f"{topology}: sending the light burst at {burst_at - node_started:.0f} s", flush=True)
                        run_workload(topology, ["--no-scenarios", "--inject", "lightburst"], work / "burst.log", 300)
                time.sleep(2)
                if time.time() - node_started > options.follow + options.reach_limit + 1200:
                    node.kill()
            sampler.stopped.set()
            summary = json.loads(report.read_text()) if report.exists() else {}
            print((work / "node.log").read_text()[-2500:])
            rows = [json.loads(line) for line in lag_log.read_text().splitlines() if line.strip()] if lag_log.exists() else []
            series = lag_series(rows, sampler.samples)
            numbers = analyse(series, node_started, options.max_lag, burst_at)
            checked, agree, problems = (peer_accept.compare_roots(topology, applied) if applied.exists()
                                        else (0, 0, ["no log"]))
            state = summary.get("stateSync") or {}
            print(json.dumps({k: summary.get(k) for k in (
                "mode", "handshakes", "disconnects", "headersAccepted", "headersDoneAtSeconds", "blocksApplied",
                "chunksApplied", "extrasChecked", "extrasAgree", "receiptsChecked", "receiptsAgree", "edgesVerified",
                "reachedHeadAtSeconds", "maxLag", "maxLagAfterHead", "meanLag", "behindSecondsAfterHead", "seconds",
                "failure")}))
            print(json.dumps({"stateSync": state}))
            print(json.dumps({"lag": numbers}))
            print("profile of the application:\n" + str(summary.get("profile")))
            checks = {
                "handshake completed": summary.get("handshakes", 0) >= 1,
                "neard lists the node among its active peers": listed,
                "state sync done, all headers and parts, none refused":
                    bool(state.get("done")) and state.get("refused", 1) == 0 and state.get("headers") == len(state.get("shards", [None])),
                f"within {options.max_lag} blocks of neard's head in {options.reach_limit} s":
                    numbers.get("reachedAfterSeconds") is not None and numbers["reachedAfterSeconds"] <= options.reach_limit,
                f"followed for {options.follow} s": numbers.get("followedSeconds", 0) >= options.follow - 5,
                "no disconnect": not summary.get("disconnects"),
                "no failure": summary.get("failure") is None and not summary.get("mismatches"),
                "ChunkExtra equal to the next chunk header's": summary.get("extrasChecked", 0) > 0
                    and summary.get("extrasChecked") == summary.get("extrasAgree"),
                "outgoing receipts equal to the next chunk body's": summary.get("receiptsChecked") == summary.get("receiptsAgree"),
                "state roots equal over RPC": checked > 0 and checked == agree,
            }
            if options.lightburst:
                checks[f"caught up after the burst within {options.catch_up_limit} s"] = (
                    numbers.get("burstCaughtUpAfterSeconds") is not None
                    and numbers["burstCaughtUpAfterSeconds"] <= options.catch_up_limit)
                checks[f"within {options.max_lag} blocks outside the burst"] = True
            else:
                checks[f"within {options.max_lag} blocks for the whole window"] = numbers.get("secondsAboveLimit", 1) == 0
            for name, good in checks.items():
                print(f"  {'ok  ' if good else 'FAIL'} {name}")
            for p in problems[:10] + summary.get("mismatches", [])[:10]:
                print("  " + p)
            print(f"{topology}: state sync at block {state.get('syncHash')}, shard start heights {state.get('startHeights')}; "
                  f"reached the head after {numbers.get('reachedAfterSeconds')} s; max lag {numbers.get('maxLagAfterReach')} "
                  f"blocks, median {numbers.get('medianLag')}; followed {numbers.get('followedSeconds')} s; "
                  f"{checked} state roots compared over RPC, {agree} equal; {len(summary.get('disconnects', []))} disconnects")
            result = all(checks.values())
    finally:
        sampler.stopped.set()
        if node is not None and node.poll() is None:
            node.kill()
        for process in background:
            if process.poll() is None:
                process.kill()
        localnet.stop(topology)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--topologies", nargs="*", default=["single", "sharded"], choices=sorted(localnet.TOPOLOGIES))
    parser.add_argument("--follow", type=int, default=600, help="seconds to follow the head once reached")
    parser.add_argument("--max-lag", type=int, default=10, help="blocks the node may trail neard's head")
    parser.add_argument("--reach-limit", type=int, default=180, help="seconds from the start to be within --max-lag")
    parser.add_argument("--catch-up-limit", type=int, default=240, help="seconds to catch up after the light burst")
    parser.add_argument("--burst-delay", type=int, default=60, help="seconds after reaching the head to send the burst")
    parser.add_argument("--lightburst", action="store_true", help="send a burst of heavy calls while following")
    parser.add_argument("--full-workload", action="store_true", help="include the heavy scenarios in the history")
    parser.add_argument("--workload-limit", type=int, default=3000, help="seconds the workload may take")
    parser.add_argument("--period", type=float, default=1.0, help="seconds between rounds of light traffic")
    parser.add_argument("--settle", type=int, default=20, help="seconds of light traffic before the node starts")
    parser.add_argument("--track", default="", help="shards the node tracks, for example 0,2 (default all)")
    parser.add_argument("--binary", type=Path, default=BINARY)
    parser.add_argument("--keep", help="a directory to keep the logs, reports and lag logs in")
    options = parser.parse_args()
    ok = True
    for topology in options.topologies:
        ok = accept(topology, options) and ok
    print("localnet-follow: " + ("all agree" if ok else "FAILED"))
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
