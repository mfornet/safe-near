from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import near_snapshot
import snapshot_vm as vm
from test_near_snapshot import FakeRPC


class SnapshotVMTests(unittest.TestCase):
    def setUp(self):
        self.snapshot = near_snapshot.capture(["app.near"], request=FakeRPC())
        self.snapshot["block"]["header"]["timestamp_nanosec"] = "1792439509598315089"
        self.scenario = {"epochHeight": 99, "randomSeed": list(range(32)), "calls": [{
            "name": "first", "method": "read", "args": {"message": "🙂"},
            "signer": "signer.near", "predecessor": "caller.near",
            "signerPublicKey": [0] + [1] * 32, "gas": 100_000_000_000_000, "view": True}]}
        self.reference_requests = []
        self.model_requests = []

    def reference(self, request):
        self.reference_requests.append(deepcopy(request))
        return {"balance": str(int(request["accountBalance"]) + 1),
                "storageUsage": request["storageUsage"], "storage": request["storage"],
                "returnData": {"kind": "value", "bytes": [0, 255]}, "gasBurnt": 100,
                "logs": [], "receipts": [], "aborted": None, "issue": None}

    def model(self, request):
        self.model_requests.append(deepcopy(request))
        return {"balance": str(int(request["accountBalance"]) + 1),
                "storageUsage": request["storageUsage"], "storage": request["storage"],
                "returnData": {"kind": "value", "bytes": [0, 255]}, "gasBurnt": 100,
                "logs": [], "receipts": [], "aborted": None, "issue": None}

    def compare(self, **kwargs):
        return vm.compare(self.snapshot, "app.near", self.scenario,
                          reference=kwargs.get("reference", self.reference),
                          model=kwargs.get("model", self.model), code_path="contract.wasm",
                          wat_path="contract.wat", config_dir="configs")

    def test_seed_preserves_identity_binary_storage_and_integer_precision(self):
        result = self.compare()
        self.assertEqual((result["passed"], result["failed"]), (1, 0))
        request = self.reference_requests[0]
        self.assertEqual(request, self.model_requests[0])
        self.assertEqual(request["currentAccountId"], "app.near")
        self.assertEqual(request["accountBalance"], "123")
        self.assertEqual(request["storageUsage"], 48)
        self.assertEqual(request["blockTimestamp"], 1792439509598315089)
        self.assertEqual(request["epochHeight"], 99)
        self.assertEqual(request["randomSeed"], list(range(32)))
        self.assertEqual(request["protocolVersion"], 86)
        self.assertIn([[97, 0], [255]], request["storage"])
        self.assertEqual(bytes(request["input"]).decode(), '{"message":"🙂"}')

    def test_reference_state_feeds_both_executors_after_disagreement(self):
        self.scenario["calls"].append({**self.scenario["calls"][0], "name": "second"})
        def wrong(request):
            result = self.model(request)
            result["balance"] = "999"
            result["gasBurnt"] = 101
            return result
        result = self.compare(model=wrong)
        self.assertEqual(result["failed"], 2)
        self.assertEqual(self.reference_requests[1]["accountBalance"], "124")
        self.assertEqual(self.reference_requests, self.model_requests)
        self.assertEqual({d["path"] for d in result["cases"][0]["differences"]},
                         {"$.balance", "$.gasBurnt"})

    def test_crash_retains_request_and_marks_remaining_calls_unrun(self):
        self.scenario["calls"].append({**self.scenario["calls"][0], "name": "second"})
        def crash(request):
            raise RuntimeError("executor crashed")
        result = self.compare(model=crash)
        self.assertEqual(result["failed"], 2)
        self.assertEqual(result["notRun"], ["second"])
        self.assertIn("reference", result["cases"][0])
        self.assertEqual(result["cases"][0]["request"]["currentAccountId"], "app.near")
        self.assertIn("executor crashed", result["cases"][0]["executionError"])

    def test_filtered_storage_cannot_be_treated_as_complete(self):
        self.snapshot["accounts"][0]["storage"]["complete"] = False
        with self.assertRaisesRegex(ValueError, "complete account storage"):
            self.compare()
        self.assertEqual(self.reference_requests, [])

    def test_tampered_code_hash_is_rejected(self):
        self.snapshot["accounts"][0]["account"]["code_hash"] = "wrong"
        with self.assertRaisesRegex(ValueError, "hash mismatch"):
            self.compare()

    def test_duplicate_storage_is_rejected(self):
        values = self.snapshot["accounts"][0]["storage"]["values"]
        values.append(values[0])
        with self.assertRaisesRegex(ValueError, "duplicate storage"):
            self.compare()

    def test_missing_epoch_context_is_not_invented(self):
        del self.scenario["epochHeight"]
        with self.assertRaises(KeyError):
            self.compare()

    def test_ambiguous_input_or_unknown_call_field_is_rejected(self):
        call = self.scenario["calls"][0]
        call["input"] = []
        with self.assertRaisesRegex(ValueError, "exactly one"):
            self.compare()
        del call["input"]
        call["currentAccountId"] = "wrong.near"
        with self.assertRaisesRegex(ValueError, "unknown call fields"):
            self.compare()

    def test_integer_bounds_and_byte_values(self):
        for value in [-1, 2 ** 64, True, 1.2]:
            self.scenario["epochHeight"] = value
            with self.assertRaises(ValueError):
                self.compare()
        self.scenario["epochHeight"] = 1
        self.scenario["randomSeed"] = [256] * 32
        with self.assertRaises(ValueError):
            self.compare()

    def test_failed_protocol_call_is_an_observation_not_a_crashed_executor(self):
        def abort(request):
            result = self.reference(request)
            result["aborted"] = "contract panic"
            result["balance"] = request["accountBalance"]
            return result
        result = self.compare(reference=abort, model=abort)
        self.assertEqual(result["passed"], 1)
        self.assertNotIn("executionError", result["cases"][0])

    def test_missing_and_null_are_different(self):
        self.assertTrue(vm.differences({"issue": None}, {}))
        self.assertTrue(vm.differences(True, 1))
        self.assertTrue(vm.differences([0], [0, 1]))

    def test_cli_freezes_executables_and_retains_configuration_evidence(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            captured, scenario, report = root / "snapshot.json", root / "scenario.json", root / "report.json"
            captured.write_text(json.dumps(self.snapshot))
            scenario.write_text(json.dumps(self.scenario))
            config = root / "configs"
            config.mkdir()
            (config / "runtime_config_v86.json").write_text('{"version":86}\n')
            executors = []
            for label in ["reference", "model"]:
                path = root / label
                path.write_text(f'''#!{sys.executable}
import json,sys
# {label}: independent test process
r=json.load(sys.stdin)
with open({str(root / (label + '.trace'))!r},'w') as f:
    json.dump({{'executable':sys.argv[0],'request':r}},f)
print(json.dumps({{'balance':r['accountBalance'],'storageUsage':r['storageUsage'],'storage':r['storage']}}))
''')
                path.chmod(0o700)
                executors.append(path)
            wasm_tools = root / "wasm-tools"
            wasm_tools.write_text(f'''#!{sys.executable}
import sys
from pathlib import Path
if sys.argv[1]=='--version': print('wasm-tools 1.251.0')
else: Path(sys.argv[sys.argv.index('-o')+1]).write_text('(module)')
''')
            wasm_tools.chmod(0o700)
            command = [sys.executable, str(Path(vm.__file__)), str(captured), "app.near", str(scenario),
                       "--reference", str(executors[0]), "--model", str(executors[1]),
                       "--config-dir", str(config), "--report", str(report)]
            environment = {**os.environ, "PATH": str(root) + os.pathsep + os.environ["PATH"]}
            process = subprocess.run(command, capture_output=True, text=True, env=environment)
            self.assertEqual(process.returncode, 0, process.stdout + process.stderr)
            evidence = json.loads(report.read_text())
            self.assertEqual(evidence["passed"], 1)
            self.assertEqual(evidence["configurationFiles"]["runtime_config_v86.json"]["text"],
                             '{"version":86}\n')
            for label, original in zip(["reference", "model"], executors):
                trace = json.loads((root / (label + ".trace")).read_text())
                self.assertNotEqual(trace["executable"], str(original))
                self.assertFalse(Path(trace["executable"]).exists(), "temporary executor was not cleaned up")
                self.assertNotEqual(trace["request"]["configDir"], str(config))
            first = report.read_bytes()
            repeated = subprocess.run(command, capture_output=True, text=True, env=environment)
            self.assertEqual(repeated.returncode, 2)
            self.assertEqual(first, report.read_bytes())


if __name__ == "__main__":
    unittest.main()
