"""Offline checks for the source provenance and isolation of the apply oracle."""

import fcntl
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[1] / "chain-conformance/prepare.py"
SPEC = importlib.util.spec_from_file_location("chain_reference_prepare", SCRIPT)
reference = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(reference)


class SourceProvenance(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="safe-near-reference-test-")
        self.addCleanup(self.temporary.cleanup)
        self.source = Path(self.temporary.name) / "source"
        self.source.mkdir()
        self.run_git("init", "--quiet")
        manifest = self.source / reference.MANIFEST
        manifest.parent.mkdir(parents=True)
        self.original = b'[package]\nname = "fixture"\n[features]\ntest_features = []\nestimator = []\n'
        manifest.write_bytes(self.original)
        (self.source / "Cargo.lock").write_text("# immutable lockfile\n")
        (self.source / "rust-toolchain.toml").write_text('[toolchain]\nchannel = "1.93.0"\n')
        (self.source / "implementation.rs").write_text("fn operation() {}\n")
        self.run_git("add", ".")
        self.run_git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                     "commit", "--quiet", "-m", "fixture")
        self.revision = self.run_git("rev-parse", "HEAD").strip()
        self.marker = self.source / ".git/safe-near-apply-overlay.json"

    def run_git(self, *arguments):
        return subprocess.check_output(["git", "-C", str(self.source), *arguments], text=True)

    def overlay(self):
        shim = b"fn main() {}\n"
        manifest = self.original + reference.STANZA
        (self.source / reference.MANIFEST).write_bytes(manifest)
        (self.source / reference.SHIM).write_bytes(shim)
        self.marker.write_text(json.dumps({"revision": self.revision,
            "manifestBefore": reference.digest(self.original), "shimSha256": reference.digest(shim)}))
        return manifest, shim

    def test_clean_source_and_exact_revision(self):
        reference.verify_source(self.source, self.revision)
        with self.assertRaisesRegex(ValueError, "pinned revision"):
            reference.verify_source(self.source, "0" * 40)
        self.assertEqual(self.run_git("status", "--porcelain"), "")

    def test_modified_implementation_is_rejected(self):
        (self.source / "implementation.rs").write_text("fn substituted() {}\n")
        with self.assertRaisesRegex(ValueError, "unrecognized"):
            reference.verify_source(self.source, self.revision)

    def test_untracked_implementation_is_rejected(self):
        (self.source / "extra.rs").write_text("fn substituted() {}\n")
        with self.assertRaisesRegex(ValueError, "unrecognized"):
            reference.verify_source(self.source, self.revision)

    def test_only_the_exact_known_overlay_is_permitted(self):
        manifest, shim = self.overlay()
        reference.verify_source(self.source, self.revision, manifest, shim)
        (self.source / reference.SHIM).write_bytes(shim + b"// altered\n")
        with self.assertRaisesRegex(ValueError, "changed during"):
            reference.verify_source(self.source, self.revision, manifest, shim)

    def test_lockfile_changes_are_never_part_of_the_overlay(self):
        manifest, shim = self.overlay()
        (self.source / "Cargo.lock").write_text("# changed\n")
        with self.assertRaisesRegex(ValueError, "unexpected source"):
            reference.verify_source(self.source, self.revision, manifest, shim)

    def test_interrupted_owned_overlay_is_recovered(self):
        self.overlay()
        reference.recover_overlay(self.source, self.revision, self.original)
        reference.verify_source(self.source, self.revision)
        self.assertFalse(self.marker.exists())

    def test_modified_interrupted_adapter_is_preserved(self):
        manifest, _ = self.overlay()
        changed = b"// user edits\n"
        (self.source / reference.SHIM).write_bytes(changed)
        with self.assertRaisesRegex(ValueError, "modified"):
            reference.recover_overlay(self.source, self.revision, self.original)
        self.assertEqual((self.source / reference.SHIM).read_bytes(), changed)
        self.assertEqual((self.source / reference.MANIFEST).read_bytes(), manifest)

    def test_changed_revision_is_rejected_before_recovery(self):
        manifest, shim = self.overlay()
        with self.assertRaisesRegex(ValueError, "pinned revision"):
            reference.build(self.source, "0" * 40, Path(self.temporary.name) / "oracle", True)
        self.assertEqual((self.source / reference.SHIM).read_bytes(), shim)
        self.assertEqual((self.source / reference.MANIFEST).read_bytes(), manifest)

    def test_failed_compiler_restores_the_clean_checkout(self):
        original_run = subprocess.run
        def failing_cargo(command, *args, **kwargs):
            if command[0] == "cargo":
                raise subprocess.CalledProcessError(101, command)
            return original_run(command, *args, **kwargs)
        with patch.object(reference.subprocess, "run", side_effect=failing_cargo):
            with self.assertRaises(subprocess.CalledProcessError):
                reference.build(self.source, self.revision, Path(self.temporary.name) / "oracle", True)
        reference.verify_source(self.source, self.revision)
        self.assertFalse(self.marker.exists())

    def test_concurrent_builder_cannot_modify_the_checkout(self):
        with (self.source / ".git/safe-near-apply.lock").open("a") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaises(BlockingIOError):
                reference.build(self.source, self.revision, Path(self.temporary.name) / "oracle", True)
        reference.verify_source(self.source, self.revision)

    def test_binary_cannot_overwrite_source(self):
        with self.assertRaisesRegex(ValueError, "outside"):
            reference.build(self.source, self.revision, self.source / reference.MANIFEST)
        reference.verify_source(self.source, self.revision)

    def test_published_binary_has_exact_bytes_and_executable_mode(self):
        original = Path(self.temporary.name) / "native"
        output = Path(self.temporary.name) / "result/oracle.json"
        payload = b"executable bytes" * 100_000
        original.write_bytes(payload)
        checksum = reference.publish_binary(original, output)
        self.assertEqual(checksum, reference.digest(payload))
        self.assertEqual(output.read_bytes(), payload)
        self.assertEqual(output.stat().st_mode & 0o777, 0o755)
        self.assertEqual(list(output.parent.iterdir()), [output])


if __name__ == "__main__":
    unittest.main()
