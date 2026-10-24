"""Deterministic NEAR transaction construction for the localnet workload (stdlib only).

Contains a pure-Python Ed25519 (RFC 8032), base58, and the Borsh encodings of the
transactions and actions that protocol 86 accepts.  Everything here is a pure
function of its inputs, so a workload built from a seed is byte-reproducible.
"""

from __future__ import annotations

import hashlib
import struct

B58 = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"


def b58encode(data: bytes) -> str:
    number = int.from_bytes(data, "big")
    text = ""
    while number:
        number, remainder = divmod(number, 58)
        text = B58[remainder] + text
    return "1" * (len(data) - len(data.lstrip(b"\0"))) + text


def b58decode(text: str) -> bytes:
    number = 0
    for character in text:
        number = number * 58 + B58.index(character)
    body = number.to_bytes((number.bit_length() + 7) // 8, "big")
    return b"\0" * (len(text) - len(text.lstrip("1"))) + body


# --- Ed25519 (RFC 8032, section 6, reference implementation) -------------------
P = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493
D = -121665 * pow(121666, P - 2, P) % P
I = pow(2, (P - 1) // 4, P)


def _recover_x(y: int, sign: int) -> int | None:
    x2 = (y * y - 1) * pow(D * y * y + 1, P - 2, P) % P
    x = pow(x2, (P + 3) // 8, P)
    if (x * x - x2) % P:
        x = x * I % P
    if (x * x - x2) % P:
        return None
    return P - x if (x & 1) != sign else x


_BY = 4 * pow(5, P - 2, P) % P
_BX = _recover_x(_BY, 0)
G = (_BX, _BY, 1, _BX * _BY % P)


def _add(p, q):
    a = (p[1] - p[0]) * (q[1] - q[0]) % P
    b = (p[1] + p[0]) * (q[1] + q[0]) % P
    c = 2 * p[3] * q[3] * D % P
    d = 2 * p[2] * q[2] % P
    e, f, g, h = b - a, d - c, d + c, b + a
    return (e * f % P, g * h % P, f * g % P, e * h % P)


def _mul(scalar: int, point):
    result = (0, 1, 1, 0)
    while scalar:
        if scalar & 1:
            result = _add(result, point)
        point = _add(point, point)
        scalar >>= 1
    return result


def _compress(point) -> bytes:
    zinv = pow(point[2], P - 2, P)
    x, y = point[0] * zinv % P, point[1] * zinv % P
    return int(y | ((x & 1) << 255)).to_bytes(32, "little")


def _decompress(data: bytes):
    y = int.from_bytes(data, "little")
    sign, y = y >> 255, y & ((1 << 255) - 1)
    x = _recover_x(y, sign)
    if x is None:
        raise ValueError("invalid point")
    return (x, y, 1, x * y % P)


def _clamp(digest: bytes) -> int:
    a = bytearray(digest[:32])
    a[0] &= 248
    a[31] &= 127
    a[31] |= 64
    return int.from_bytes(a, "little")


def ed25519_public(seed: bytes) -> bytes:
    return _compress(_mul(_clamp(hashlib.sha512(seed).digest()), G))


def ed25519_sign(seed: bytes, message: bytes) -> bytes:
    digest = hashlib.sha512(seed).digest()
    a = _clamp(digest)
    public = _compress(_mul(a, G))
    r = int.from_bytes(hashlib.sha512(digest[32:] + message).digest(), "little") % L
    big_r = _compress(_mul(r, G))
    k = int.from_bytes(hashlib.sha512(big_r + public + message).digest(), "little") % L
    return big_r + ((r + k * a) % L).to_bytes(32, "little")


def ed25519_verify(public: bytes, message: bytes, signature: bytes) -> bool:
    try:
        a, r = _decompress(public), _decompress(signature[:32])
    except ValueError:
        return False
    s = int.from_bytes(signature[32:], "little")
    if s >= L:
        return False
    k = int.from_bytes(hashlib.sha512(signature[:32] + public + message).digest(), "little") % L
    left, right = _mul(s, G), _add(r, _mul(k, a))
    return _compress(left) == _compress(right)


# --- Borsh ---------------------------------------------------------------------
def u8(n): return struct.pack("<B", n)
def u32(n): return struct.pack("<I", n)
def u64(n): return struct.pack("<Q", n)
def u128(n): return n.to_bytes(16, "little")
def string(s): return u32(len(s.encode())) + s.encode()
def vec(items): return u32(len(items)) + b"".join(items)
def blob(b): return u32(len(b)) + bytes(b)
def option(item): return u8(0) if item is None else u8(1) + item


class Key:
    """An Ed25519 key pair derived from a 32-byte seed."""

    def __init__(self, seed: bytes):
        self.seed = seed
        self.public = ed25519_public(seed)

    @classmethod
    def derive(cls, label: str) -> "Key":
        return cls(hashlib.sha256(b"safe-near-localnet/" + label.encode()).digest())

    @classmethod
    def from_secret(cls, text: str) -> "Key":
        raw = b58decode(text.split(":", 1)[1])
        return cls(raw[:32])

    @property
    def pk(self) -> bytes:           # Borsh PublicKey
        return u8(0) + self.public

    @property
    def text(self) -> str:
        return "ed25519:" + b58encode(self.public)

    def sign(self, message: bytes) -> bytes:
        return u8(0) + ed25519_sign(self.seed, message)   # Borsh Signature


# Actions (tags from core/primitives/src/action/mod.rs, protocol 86).
def create_account(): return u8(0)
def deploy_contract(code): return u8(1) + blob(code)
def function_call(method, args, gas, deposit=0):
    return u8(2) + string(method) + blob(args) + u64(gas) + u128(deposit)
def transfer(deposit): return u8(3) + u128(deposit)
def stake(amount, public_key): return u8(4) + u128(amount) + public_key
def add_key(public_key, access_key): return u8(5) + public_key + access_key
def delete_key(public_key): return u8(6) + public_key
def delete_account(beneficiary): return u8(7) + string(beneficiary)
def delegate(signed_delegate): return u8(8) + signed_delegate
def deploy_global_contract(code, by_account: bool): return u8(9) + blob(code) + u8(1 if by_account else 0)
def use_global_contract_by_hash(code_hash: bytes): return u8(10) + u8(0) + code_hash
def use_global_contract_by_account(account): return u8(10) + u8(1) + string(account)
def transfer_to_gas_key(public_key, deposit): return u8(12) + public_key + u128(deposit)
def withdraw_from_gas_key(public_key, amount): return u8(13) + public_key + u128(amount)


def access_key_full(nonce=0): return u64(nonce) + u8(1)
def access_key_function_call(receiver, methods, allowance=None, nonce=0):
    return u64(nonce) + u8(0) + option(None if allowance is None else u128(allowance)) \
        + string(receiver) + vec([string(m) for m in methods])
def access_key_gas_full(num_nonces, nonce=0):
    # GasKeyInfo { balance: u128, num_nonces: u16 }
    return u64(nonce) + u8(3) + u128(0) + struct.pack("<H", num_nonces)


def delegate_action(sender, receiver, actions, nonce, max_block_height, public_key):
    return string(sender) + string(receiver) + vec(actions) + u64(nonce) + u64(max_block_height) + public_key


def signed_delegate(key: Key, action: bytes) -> bytes:
    # NEP-461: sha256(u32 discriminant 2^30 + 366 || borsh(DelegateAction))
    digest = hashlib.sha256(u32((1 << 30) + 366) + action).digest()
    return action + key.sign(digest)


def transaction(signer, key: Key, nonce, receiver, block_hash: bytes, actions) -> bytes:
    body = string(signer) + key.pk + u64(nonce) + string(receiver) + block_hash + vec(actions)
    return body + key.sign(hashlib.sha256(body).digest())


def transaction_v1_strict(signer, key: Key, nonce, receiver, block_hash: bytes, actions) -> bytes:
    # TransactionV1: 0x01 tag; nonce = TransactionNonce::Nonce{nonce}; NonceMode::Strict
    body = (u8(1) + string(signer) + key.pk + u8(0) + u64(nonce) + string(receiver) + block_hash
            + vec(actions) + u8(1))
    return body + key.sign(hashlib.sha256(body).digest())


def transaction_hash(signed: bytes) -> bytes:
    # hash of the Borsh transaction body: everything before the 65-byte signature
    return hashlib.sha256(signed[:-65]).digest()
