#!/usr/bin/env python3
"""Soak of the validator (M10): `just localnet-soak`.

The topology of `just localnet-validator` (two validators of equal stake, one shard, or with `--topology validator-sharded` four; node0 is `neard`, node1 the Lean
node, so the chain cannot finalize without the Lean node) with the full workload on it for a long window: the
scenarios of ``workload.py`` once (host function calls, the 14 calls of 300 Tgas, the wait for a yield to time
out), then light traffic all the time and, every ``--burst-period`` seconds, a light burst (ten calls that each
run millions of instructions, in one block).

While it runs a sampler reads, every ``--sample`` seconds: the head and the final height of `neard`, the head of the
Lean node over its own JSON-RPC (which must answer: ``status``, a ``block`` and a ``query``), its resident set size, and the
size of its store.  A checker follows the Lean node's applied-blocks log and compares the hash of every block with
`neard`'s and the state root of every shard with the ``prev_state_root`` of the next block's chunk as `neard` returns it.

Checks (the numbers go to ``soak.json`` in the work directory):

* every state root and block hash equal (and at least one per ten blocks compared);
* the final height advances in every window of ``--window`` seconds, and trails the head by less than 20 blocks;
* the Lean node trails `neard`'s head by at most ``--max-lag`` blocks at every sample outside a burst (a burst: the
  ``--burst-window`` seconds from the time the workload sends it); the peak lag inside a burst is reported;
* no disconnect, no failure, the Lean node never exits;
* the RPC of the Lean node answers at every sample;
* resident memory bounded: the slope of a least-squares line through the samples after the first ``--warmup``
  seconds is below ``--max-rss-slope`` MB per hour;
* store growth reported (bytes per hour).
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import signal
import statistics
import subprocess
import sys
import threading
import time
import urllib.request

import localnet
import nearcodec as nc
import validator_accept as va

HERE = Path(__file__).resolve().parent
LEAN_RPC = ("127.0.0.1", 18399)


def lean_rpc(method: str, params, timeout: float = 5):
    body = json.dumps({"jsonrpc": "2.0", "id": "soak", "method": method, "params": params}).encode()
    request = urllib.request.Request(f"http://{LEAN_RPC[0]}:{LEAN_RPC[1]}", data=body,
                                     headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(request, timeout=timeout) as reply:
        return json.loads(reply.read())


def rss_kb(pid: int) -> int | None:
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1])
    except OSError:
        return None
    return None


def tree_bytes(path: Path) -> int:
    total = 0
    for root, _, files in os.walk(path):
        for name in files:
            try:
                total += (Path(root) / name).stat().st_size
            except OSError:
                pass
    return total


def slope_per_hour(points: list[tuple[float, float]]) -> float:
    """Least-squares slope of (seconds, value) in value units per hour."""
    if len(points) < 3:
        return 0.0
    xs = [p[0] for p in points]
    ys = [p[1] for p in points]
    mx, my = statistics.fmean(xs), statistics.fmean(ys)
    denominator = sum((x - mx) ** 2 for x in xs)
    if denominator == 0:
        return 0.0
    return sum((x - mx) * (y - my) for x, y in points) / denominator * 3600


class Soak:
    def __init__(self, options: argparse.Namespace, lean: subprocess.Popen, store: Path, work: Path):
        self.options = options
        self.lean = lean
        self.store = store
        self.work = work
        self.started = time.time()
        self.samples: list[dict] = []
        self.bursts: list[float] = []
        self.rpc_failures: list[str] = []
        self.compared = {"blocks": 0, "hashEqual": 0, "orphans": 0, "roots": 0, "rootsEqual": 0, "problems": []}
        self.applied_offset = 0
        self.pending: list[dict] = []
        self.stop = threading.Event()
        self.restarts = 0
        self.pauses: list[float] = []     # when the Lean node was restarted: its catching up is not held to the lag bound

    def restart(self, home: Path, binary: Path, extra: list[str], duration: int) -> subprocess.Popen:
        """SIGKILL of the Lean node, and a start from its store eight seconds later (the applied-blocks log of the
        new process starts over, so the checker reads it from the beginning)."""
        self.check_blocks()
        os.killpg(self.lean.pid, signal.SIGKILL)
        self.lean.wait()
        time.sleep(8)
        self.lean = va.start_lean(home, self.work, duration, binary, extra, log_name="lean-restart.log")
        self.applied_offset = 0
        self.restarts += 1
        self.pauses.append(time.time())
        return self.lean

    def in_burst(self, t: float) -> bool:
        return any(b <= t <= b + self.options.burst_window for b in self.bursts + self.pauses)

    def sample(self) -> None:
        now = time.time()
        row: dict = {"t": round(now - self.started, 1), "unix": now, "leanAlive": self.lean.poll() is None}
        try:
            row["neardHead"] = va.head_height()
            row["neardFinal"] = va.final_height()
        except Exception as error:      # noqa: BLE001
            row["neardError"] = str(error)[:100]
        try:
            status = lean_rpc("status", [])["result"]
            row["leanHead"] = status["sync_info"]["latest_block_height"]
            lean_rpc("block", {"finality": "final"})
            lean_rpc("gas_price", [None])
            lean_rpc("query", {"request_type": "view_account", "finality": "final", "account_id": "test1.node0"})
        except Exception as error:      # noqa: BLE001
            if not any(p <= now <= p + 90 for p in self.pauses):
                self.rpc_failures.append(f"t={row['t']}: {str(error)[:120]}")
            row["rpcError"] = True
        row["rssKb"] = rss_kb(self.lean.pid)
        row["storeBytes"] = tree_bytes(self.store)
        row["inBurst"] = self.in_burst(now)
        self.samples.append(row)

    def check_blocks(self) -> None:
        """Compare the blocks the Lean node applied since the last call with neard's."""
        path = self.work / "applied.jsonl"
        if not path.exists():
            return
        data = path.read_bytes()
        end = data.rfind(b"\n") + 1
        fresh = data[self.applied_offset:end]
        self.applied_offset = end
        rows = [json.loads(line) for line in fresh.decode().splitlines() if line.strip()]
        self.pending += rows
        still = []
        for row in self.pending:
            try:
                block = va.rpc("block", {"block_id": row["height"]})
            except Exception:           # noqa: BLE001  (a skipped height, or not there yet)
                if row["height"] < self.last_neard_head() - 3:
                    # a block the Lean node applied at a height neard skipped is an orphan, fine if neard holds it
                    if va.neard_holds(row["hash"]):
                        self.compared["orphans"] += 1
                    else:
                        self.compared["problems"].append(f"height {row['height']}: neard has no block")
                    continue
                still.append(row)
                continue
            self.compared["blocks"] += 1
            if nc.b58decode(block["header"]["hash"]).hex() == row["hash"]:
                self.compared["hashEqual"] += 1
            else:
                # an orphan: neard must hold the block all the same
                if not va.neard_holds(row["hash"]):
                    self.compared["problems"].append(f"height {row['height']}: block differs and neard lacks it")
                continue
            try:
                nxt = va.rpc("block", {"block_id": row["height"] + 1})
            except Exception:           # noqa: BLE001
                if row["height"] >= self.last_neard_head() - 1:
                    still.append(row)
                continue
            for chunk, mine in zip(nxt["chunks"], row["chunks"]):
                if chunk["height_included"] == row["height"] + 1:
                    self.compared["roots"] += 1
                    if nc.b58decode(chunk["prev_state_root"]).hex() == mine["stateRoot"]:
                        self.compared["rootsEqual"] += 1
                    else:
                        self.compared["problems"].append(f"height {row['height']}: state root differs")
        self.pending = still

    def last_neard_head(self) -> int:
        for row in reversed(self.samples):
            if "neardHead" in row:
                return row["neardHead"]
        return 0


def workload_thread(options: argparse.Namespace, soak: Soak, work: Path) -> threading.Thread:
    def run() -> None:
        python = sys.executable
        script = str(HERE / "workload.py")
        skip = ([] if options.full_workload else ["hostcalls", "burst", "wait"]) + options.skip
        # the scenarios once, then light traffic until the end
        leave_out = ["--no-deploy-from-memory"] if options.no_deploy_from_memory else []
        scenario = subprocess.Popen([python, script, va.TOPOLOGY, *leave_out, "--skip"] + skip,
                                    stdout=(work / "workload.log").open("w"), stderr=subprocess.STDOUT, cwd=HERE)
        steady_left = options.duration + 600
        deadline = soak.started + options.duration
        while scenario.poll() is None and not soak.stop.is_set():
            time.sleep(1)
        steady = subprocess.Popen([python, script, va.TOPOLOGY, "--no-scenarios", "--steady", str(steady_left),
                                   "--period", str(options.period)], stdout=(work / "steady.log").open("w"),
                                  stderr=subprocess.STDOUT, cwd=HERE)
        next_burst = time.time() + options.burst_period
        while not soak.stop.is_set() and time.time() < deadline:
            if time.time() >= next_burst:
                soak.bursts.append(time.time())
                burst = subprocess.Popen([python, script, va.TOPOLOGY, "--no-scenarios", "--inject", "lightburst"],
                                         stdout=(work / "burst.log").open("a"), stderr=subprocess.STDOUT, cwd=HERE)
                try:
                    burst.wait(timeout=300)
                except subprocess.TimeoutExpired:
                    burst.kill()
                next_burst += options.burst_period
            time.sleep(1)
        for process in (steady, scenario):
            if process.poll() is None:
                process.kill()

    thread = threading.Thread(target=run, daemon=True)
    thread.start()
    return thread


def summarize(options: argparse.Namespace, soak: Soak, report: dict) -> dict:
    samples = soak.samples
    both = [s for s in samples if "neardHead" in s and "leanHead" in s]
    lags = [(s, max(0, s["neardHead"] - s["leanHead"])) for s in both]
    outside = [lag for s, lag in lags if not s["inBurst"]]
    inside = [lag for s, lag in lags if s["inBurst"]]
    rss = [(s["t"], s["rssKb"] / 1024) for s in samples if s.get("rssKb") and s["t"] >= options.warmup]
    allrss = [s["rssKb"] / 1024 for s in samples if s.get("rssKb")]
    store = [(s["t"], s["storeBytes"]) for s in samples if s.get("storeBytes") is not None]
    finals = [(s["t"], s["neardFinal"]) for s in samples if "neardFinal" in s]
    stuck = []
    window = options.window
    for i, (t, f) in enumerate(finals):
        later = [g for u, g in finals if t < u <= t + window]
        if later and max(later) <= f and t + window <= finals[-1][0]:
            stuck.append(round(t))
    final_lag = max((s["neardHead"] - s["neardFinal"] for s in samples if "neardFinal" in s and "neardHead" in s), default=None)
    duration = samples[-1]["t"] if samples else 0
    result = {
        "durationSeconds": duration, "samples": len(samples), "bursts": len(soak.bursts),
        "blocksCompared": soak.compared["blocks"], "blockHashesEqual": soak.compared["hashEqual"],
        "stateRootsCompared": soak.compared["roots"], "stateRootsEqual": soak.compared["rootsEqual"],
        "orphansHeldByNeard": soak.compared["orphans"], "restarts": soak.restarts,
        "problems": soak.compared["problems"][:10],
        "neardHeadStart": both[0]["neardHead"] if both else None, "neardHeadEnd": both[-1]["neardHead"] if both else None,
        "finalHeightEnd": finals[-1][1] if finals else None, "maxHeadMinusFinal": final_lag,
        "windowsWithoutFinality": stuck[:10],
        "maxLagOutsideBurst": max(outside, default=None), "maxLagInBurst": max(inside, default=None),
        "medianLag": statistics.median([lag for _, lag in lags]) if lags else None,
        "rssMbStart": round(statistics.fmean([r for _, r in rss][:6]), 1) if rss else None,
        "rssMbEnd": round(statistics.fmean([r for _, r in rss][-6:]), 1) if rss else None,
        "rssMbMax": round(max(allrss), 1) if allrss else None,
        "rssSlopeMbPerHour": round(slope_per_hour(rss), 2),
        "storeBytesStart": store[0][1] if store else None, "storeBytesEnd": store[-1][1] if store else None,
        "storeBytesPerHour": round(slope_per_hour([(t, float(b)) for t, b in store])),
        "rpcFailures": len(soak.rpc_failures), "rpcFailureExamples": soak.rpc_failures[:5],
        "disconnects": [d for d in report.get("disconnects", []) if "connection refused" not in d],
        "failure": report.get("failure"), "leanStats": report.get("stats", {}),
    }
    checks = {
        "state roots and block hashes equal": soak.compared["roots"] > 0 and soak.compared["rootsEqual"] == soak.compared["roots"]
            and soak.compared["hashEqual"] + len(soak.compared["problems"]) <= soak.compared["blocks"]
            and not soak.compared["problems"],
        "enough blocks compared": soak.compared["blocks"] >= max(10, (result["neardHeadEnd"] or 0) // 10),
        "finality advances in every window": not stuck and finals != [],
        "head minus final under 20": final_lag is not None and final_lag < 20,
        f"lag at most {options.max_lag} outside bursts": bool(outside) and max(outside) <= options.max_lag,
        "no disconnect, no failure": not result["disconnects"] and not result["failure"],
        "Lean node alive at every sample": all(s["leanAlive"] for s in samples),
        "RPC answered at every sample": not soak.rpc_failures,
        f"RSS slope under {options.max_rss_slope} MB/h": result["rssSlopeMbPerHour"] < options.max_rss_slope,
    }
    result["checks"] = checks
    result["ok"] = all(checks.values())
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--topology", default="validator", choices=sorted(t for t, spec in localnet.TOPOLOGIES.items() if spec.get("neard")),
                        help="validator: one shard; validator-sharded: the four shards of `sharded`")
    parser.add_argument("--duration", type=int, default=3600, help="seconds of soak")
    parser.add_argument("--sample", type=float, default=5.0, help="seconds between samples")
    parser.add_argument("--burst-period", type=int, default=300, help="seconds between light bursts")
    parser.add_argument("--burst-window", type=int, default=90, help="seconds after a burst in which lag is not bounded")
    parser.add_argument("--window", type=int, default=120, help="seconds in which the final height must advance")
    parser.add_argument("--max-lag", type=int, default=10)
    parser.add_argument("--warmup", type=int, default=600, help="seconds before the RSS slope is measured")
    parser.add_argument("--max-rss-slope", type=float, default=200.0, help="MB per hour")
    parser.add_argument("--period", type=float, default=1.0, help="seconds between rounds of light traffic")
    parser.add_argument("--no-full-workload", dest="full_workload", action="store_false",
                        help="leave out the host function calls, the 14 heavy calls and the yield wait")
    parser.add_argument("--restart-at", type=int, default=0,
                        help="SIGKILL the Lean node this many seconds in and start it again from its store")
    parser.add_argument("--gc-epochs", type=int, default=None,
                        help="--gc-epochs-to-keep of the Lean node (default: its own, 5; 0 collects nothing)")
    parser.add_argument("--verbose", action="store_true", help="let the Lean node log (lean.log in the work directory)")
    parser.add_argument("--skip", nargs="*", default=[], help="more scenarios of workload.py to leave out")
    parser.add_argument("--no-deploy-from-memory", action="store_true",
                        help="leave out the call that deploys contract code from a contract's memory (`sanity_check`)")
    parser.add_argument("--binary", type=Path, default=va.BINARY)
    parser.add_argument("--work", type=Path, default=localnet.DATA / "soak-run")
    options = parser.parse_args()
    va.set_topology(options.topology)
    work = options.work
    home = va.prepare(work)
    store = work / "store"
    localnet.start(va.TOPOLOGY)
    extra = ["--rpc-addr", f"{LEAN_RPC[0]}:{LEAN_RPC[1]}", "--store", str(store)] + ([] if options.verbose else ["--quiet"]) \
        + (["--gc-epochs-to-keep", str(options.gc_epochs)] if options.gc_epochs is not None else [])
    lean = va.start_lean(home, work, options.duration + 600, options.binary, extra)
    soak = Soak(options, lean, store, work)
    result: dict = {"ok": False}
    try:
        va.wait_for(lambda: va.head_height() >= 3, 120, "the chain did not start")
        soak.started = time.time()
        thread = workload_thread(options, soak, work)
        next_check = 0.0
        while time.time() - soak.started < options.duration:
            if options.restart_at and soak.restarts == 0 and time.time() - soak.started >= options.restart_at:
                lean = soak.restart(home, options.binary, extra, options.duration + 600)
            soak.sample()
            if time.time() >= next_check:
                soak.check_blocks()
                next_check = time.time() + 30
            if lean.poll() is not None:
                break
            time.sleep(options.sample)
        soak.stop.set()
        (work / "stop").write_text("stop")
        try:
            lean.wait(timeout=90)
        except subprocess.TimeoutExpired:
            pass
        soak.check_blocks()
        report = json.loads((work / "report.json").read_text()) if (work / "report.json").exists() else {}
        result = summarize(options, soak, report)
        (work / "soak.json").write_text(json.dumps({"result": result, "samples": soak.samples}, indent=1) + "\n")
        print(json.dumps(result, indent=1))
        for name, good in result["checks"].items():
            print(f"  {'ok  ' if good else 'FAIL'} {name}")
        print("localnet-soak: " + ("all agree" if result["ok"] else "FAILED"))
    finally:
        soak.stop.set()
        try:
            os.killpg(lean.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        localnet.stop(va.TOPOLOGY)
    sys.exit(0 if result["ok"] else 1)


if __name__ == "__main__":
    main()
