"""Configuration checks may omit only the known native backend selector."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location("runtime_configs", Path(__file__).resolve().parents[1] / "check_runtime_configs.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class RuntimeConfigTests(unittest.TestCase):
    def test_backend_normalization_preserves_other_fields_and_source(self):
        value = {"wasm_config": {"vm_kind": "Wasmtime", "gas": 7}, "fee": "4"}
        before = copy.deepcopy(value)
        normalized, backend = checker.normalized(value)
        self.assertEqual(value, before)
        self.assertEqual(backend, "Wasmtime")
        self.assertEqual(normalized, {"wasm_config": {"gas": 7}, "fee": "4"})
        with self.assertRaises(ValueError):
            checker.normalized({"wasm_config": {"vm_kind": "unknown"}})
        with self.assertRaises(KeyError):
            checker.normalized({"wasm_config": {}})

    def test_only_backend_difference_is_accepted(self):
        with tempfile.TemporaryDirectory() as directory:
            left, right = Path(directory) / "left", Path(directory) / "right"
            left.mkdir()
            right.mkdir()
            original = {"wasm_config": {"vm_kind": "Wasmtime", "gas": 7}, "runtime_finance": {"penalty": 3}}
            actual = copy.deepcopy(original)
            actual["wasm_config"]["vm_kind"] = "NearVm"
            name = "runtime_config_v86.json"
            (left / name).write_text(json.dumps(original))
            (right / name).write_text(json.dumps(actual))
            self.assertEqual(checker.compare(left, right), (1, [(name, "Wasmtime", "NearVm")]))
            for section, key in [("wasm_config", "gas"), ("runtime_finance", "penalty")]:
                changed = copy.deepcopy(actual)
                changed[section][key] += 1
                (right / name).write_text(json.dumps(changed))
                with self.assertRaises(ValueError):
                    checker.compare(left, right)
            (right / name).unlink()
            with self.assertRaises(ValueError):
                checker.compare(left, right)
            (right / name).write_text(json.dumps(actual))
            (right / "extra.json").write_text("{}")
            with self.assertRaises(ValueError):
                checker.compare(left, right)
