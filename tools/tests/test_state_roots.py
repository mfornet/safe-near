"""The case files `tools/localnet/state_roots.py` writes for `node-state-roots` and the store tests."""
from pathlib import Path
import struct
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[0] / "localnet"))
import corpus  # noqa: E402
import state_roots  # noqa: E402


def parse(data: bytes):
    """The reference reader of the format documented in NodeConformance/StateRoots.lean."""
    pos = 0

    def take(n):
        nonlocal pos
        assert pos + n <= len(data), "truncated"
        out = data[pos:pos + n]
        pos += n
        return out

    def u32():
        return struct.unpack("<I", take(4))[0]

    def blob():
        return take(u32())

    def entries():
        return [(blob(), blob()) for _ in range(u32())]

    assert take(4) == b"NSR1"
    pre_root = take(32)
    pre = entries()
    diff = []
    for _ in range(u32()):
        key = blob()
        diff.append((key, blob() if take(1) == b"\x01" else None))
    post_root = take(32)
    replayed = entries() if take(1) == b"\x01" else None
    assert pos == len(data)
    return pre_root, pre, diff, post_root, replayed


BUNDLE = {
    "preState": {"root": "11" * 32, "entries": [["00aa", "0102"], ["09bb2c01", ""]]},
    "expected": {"postStateRoot": "22" * 32, "stateDiff": [["00aa", "ff"], ["09bb2c01", None], ["0c", "00"]]},
}


class CaseFileTests(unittest.TestCase):
    def test_round_trip_without_replay(self):
        pre_root, pre, diff, post_root, replayed = parse(state_roots.encode_case(BUNDLE, None))
        self.assertEqual(pre_root, bytes.fromhex("11" * 32))
        self.assertEqual(pre, [(b"\x00\xaa", b"\x01\x02"), (b"\x09\xbb\x2c\x01", b"")])
        self.assertEqual(diff, [(b"\x00\xaa", b"\xff"), (b"\x09\xbb\x2c\x01", None), (b"\x0c", b"\x00")])
        self.assertEqual(post_root, bytes.fromhex("22" * 32))
        self.assertIsNone(replayed)

    def test_replayed_post_state_is_sorted(self):
        post = {b"\x09z": b"2", b"\x00a": b"1"}
        *_, replayed = parse(state_roots.encode_case(BUNDLE, post))
        self.assertEqual(replayed, [(b"\x00a", b"1"), (b"\x09z", b"2")])

    def test_every_committed_chunk_is_encodable(self):
        directory = corpus.chunk_dirs(corpus.DEFAULT_CORPUS)[0]
        bundle = corpus.unpack(directory, corpus.DEFAULT_CORPUS)
        pre_root, pre, diff, post_root, _ = parse(state_roots.encode_case(bundle, None))
        self.assertEqual(pre_root.hex(), bundle["preState"]["root"])
        self.assertEqual(len(pre), len(bundle["preState"]["entries"]))
        self.assertEqual(len(diff), len(bundle["expected"]["stateDiff"]))
        self.assertEqual(post_root.hex(), bundle["expected"]["postStateRoot"])


if __name__ == "__main__":
    unittest.main()
