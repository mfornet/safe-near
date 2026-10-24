"""A tiny deterministic WebAssembly module writer for the host-function contracts (stdlib only).

``hostcalls()`` returns a contract whose methods each call one cryptographic host
function once (``ecrecover``, ``ed25519_verify``, ``p256_verify``) on fixed vectors taken from
nearcore's estimator contract and return the host result with ``value_return``.
"""

from __future__ import annotations


def uleb(n: int) -> bytes:
    out = bytearray()
    while True:
        byte = n & 0x7F
        n >>= 7
        if n:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            return bytes(out)


def sleb(n: int) -> bytes:
    out = bytearray()
    while True:
        byte = n & 0x7F
        n >>= 7
        if (n == 0 and not byte & 0x40) or (n == -1 and byte & 0x40):
            out.append(byte)
            return bytes(out)
        out.append(byte | 0x80)


def name(text: str) -> bytes:
    raw = text.encode()
    return uleb(len(raw)) + raw


def section(section_id: int, body: bytes) -> bytes:
    return bytes([section_id]) + uleb(len(body)) + body


def vec(items: list[bytes]) -> bytes:
    return uleb(len(items)) + b"".join(items)


I64 = 0x7E
HASH = bytes.fromhex("7dbaf558b0a1a5dc7a67202117ab143c1d8605a983e4a743bc06fcc03162dc0d")
SIG = bytes.fromhex(
    "5d99b6f7f6d1f73d1a26497f2b1c89b24c0993913f86e9a2d02cd69887d9c94f"
    "3c880358579d811b21dd1b7fd9bb01c1d81d10e69f0384e675c32b39643be892")
ED_PK = bytes([51, 132, 48, 39, 30, 18, 162, 8, 235, 208, 167, 12, 35, 248, 44, 190, 223, 165, 17, 78,
               173, 129, 223, 70, 90, 104, 30, 140, 79, 201, 98, 80])
ED_MSG = b"kajdlfkjalkfjaklfjdkladjfkljadsk"
ED_SIG = bytes([149, 193, 241, 158, 225, 107, 146, 130, 116, 224, 233, 136, 232, 153, 211, 60, 115, 141,
                183, 174, 15, 52, 27, 186, 34, 68, 124, 158, 81, 3, 8, 76, 93, 28, 91, 68, 252, 151, 172,
                240, 129, 224, 239, 135, 26, 141, 111, 133, 134, 22, 149, 132, 90, 150, 33, 113, 191, 76,
                109, 64, 0, 13, 104, 6])


def hostcalls() -> bytes:
    # memory layout
    layout = [HASH, SIG, ED_PK, ED_MSG, ED_SIG]
    offsets, position = [], 0
    for blob in layout:
        offsets.append(position)
        position += len(blob)
    result = (position + 7) // 8 * 8
    types = [
        b"\x60" + vec([bytes([I64])] * 7) + vec([bytes([I64])]),   # 0: ecrecover
        b"\x60" + vec([bytes([I64])] * 6) + vec([bytes([I64])]),   # 1: ed25519_verify / p256_verify
        b"\x60" + vec([bytes([I64])] * 2) + vec([]),               # 2: value_return
        b"\x60" + vec([]) + vec([]),                               # 3: exported methods
    ]
    imports = [
        name("env") + name("ecrecover") + b"\x00" + uleb(0),
        name("env") + name("ed25519_verify") + b"\x00" + uleb(1),
        name("env") + name("p256_verify") + b"\x00" + uleb(1),
        name("env") + name("value_return") + b"\x00" + uleb(2),
    ]
    c = lambda value: b"\x42" + sleb(value)            # i64.const
    store = b"\x37\x03\x00"                              # i64.store align=3 offset=0

    def body(call: bytes) -> bytes:
        address = b"\x41" + sleb(result)                    # i32.const: memory addresses are i32 in Wasm
        code = address + call + b"\x37\x03\x00" + c(8) + c(result) + b"\x10" + uleb(3) + b"\x0b"
        return uleb(len(code) + 1) + b"\x00" + code

    ecrecover = c(32) + c(offsets[0]) + c(64) + c(offsets[1]) + c(0) + c(0) + c(0) + b"\x10" + uleb(0)
    ed25519 = c(64) + c(offsets[4]) + c(32) + c(offsets[3]) + c(32) + c(offsets[2]) + b"\x10" + uleb(1)
    # p256_verify on the ed25519 vector: exercises the host function and returns its (negative) result
    p256 = c(64) + c(offsets[4]) + c(32) + c(offsets[3]) + c(32) + c(offsets[2]) + b"\x10" + uleb(2)
    functions = [body(ecrecover), body(ed25519), body(p256)]
    exports = [
        name("memory") + b"\x02" + uleb(0),
        name("ecrecover_once") + b"\x00" + uleb(4),
        name("ed25519_once") + b"\x00" + uleb(5),
        name("p256_once") + b"\x00" + uleb(6),
    ]
    data = b"".join(layout)
    module = b"\x00asm\x01\x00\x00\x00"
    module += section(1, vec(types))
    module += section(2, vec(imports))
    module += section(3, vec([uleb(3)] * 3))
    module += section(5, vec([b"\x00" + uleb(1)]))
    module += section(7, vec(exports))
    module += section(10, vec(functions))
    module += section(11, vec([b"\x00\x41\x00\x0b" + uleb(len(data)) + data]))
    return module


def noop_contract() -> bytes:
    """A module with only `noop`, small enough to pass as an argument."""
    types = [b"\x60" + vec([]) + vec([])]
    module = b"\x00asm\x01\x00\x00\x00"
    module += section(1, vec(types))
    module += section(3, vec([uleb(0)]))
    module += section(5, vec([b"\x00" + uleb(1)]))
    module += section(7, vec([name("noop") + b"\x00" + uleb(0)]))
    module += section(10, vec([uleb(2) + b"\x00\x0b"]))
    return module
