import NearCrypto.Keccak

/-!
# SHAKE128, SHAKE256 and SHA3-256

The extendable-output functions of FIPS 202: Keccak-f[1600] with the rate of 168 and 136 bytes,
the domain bits `1111` appended to the message (the padded block starts `0x1f` and ends `0x80`)
and an output of any length, squeezed block by block. SHA3-256 is the same sponge with the rate of
136 bytes, the domain bits `01` (`0x06`) and 32 bytes of output; `near-crypto` hashes an ML-DSA-65
public key with it (`MlDsa65PublicKey::to_public_key_handle`). `Spec` is the definition over lists on
the `Keccak.Spec` permutation; `Impl` reuses the unrolled `Keccak.Impl` round and also exposes the
sponge block by block (`Xof`), which is how ML-DSA samples.
-/

namespace NearCrypto.Shake

/-! ### Spec -/

namespace Spec

open Keccak.Spec

/-- Pad10*1 after the domain byte `d` (`0x1f` for SHAKE, `0x06` for SHA-3), to a multiple of `rate`
bytes. -/
def padXof (d : UInt8) (rate : Nat) (m : List UInt8) : List UInt8 :=
  let q := rate - m.length % rate
  if q = 1 then m ++ [d ||| 0x80] else m ++ [d] ++ List.replicate (q - 2) 0 ++ [0x80]

/-- `blocks` blocks of output of `rate` bytes: squeeze, permute, repeat. -/
def squeezeBlocks (rate : Nat) (a : State) : Nat → List UInt8
  | 0 => []
  | blocks + 1 => squeeze a rate ++ squeezeBlocks rate (permute a) blocks

/-- The sponge with the domain byte `d`, `rate` bytes of rate and `n` bytes of output. -/
def xof (d : UInt8) (rate : Nat) (m : List UInt8) (n : Nat) : List UInt8 :=
  let a :=
    (SpecConstants.chunks rate (padXof d rate m)).foldl (fun a blk => permute (absorb a blk))
      (Array.replicate 25 0)
  (squeezeBlocks rate a ((n + rate - 1) / rate)).take n

/-- SHAKE128. -/
def shake128 (m : ByteArray) (n : Nat) : ByteArray :=
  ⟨(xof 0x1f 168 m.toList n).toArray⟩

/-- SHAKE256. -/
def shake256 (m : ByteArray) (n : Nat) : ByteArray :=
  ⟨(xof 0x1f 136 m.toList n).toArray⟩

/-- SHA3-256. -/
def sha3_256 (m : ByteArray) : ByteArray :=
  ⟨(xof 0x06 136 m.toList 32).toArray⟩

end Spec

/-! ### Impl -/

namespace Impl

/-- The `lane`-th lane of the state. -/
@[inline]
def lane (s : Keccak.Impl.State) : Nat → UInt64
  | 0 => s.a0
  | 1 => s.a1
  | 2 => s.a2
  | 3 => s.a3
  | 4 => s.a4
  | 5 => s.a5
  | 6 => s.a6
  | 7 => s.a7
  | 8 => s.a8
  | 9 => s.a9
  | 10 => s.a10
  | 11 => s.a11
  | 12 => s.a12
  | 13 => s.a13
  | 14 => s.a14
  | 15 => s.a15
  | 16 => s.a16
  | 17 => s.a17
  | 18 => s.a18
  | 19 => s.a19
  | 20 => s.a20
  | 21 => s.a21
  | 22 => s.a22
  | 23 => s.a23
  | _ => s.a24

/-- A sponge that has absorbed its input and pads: the next `block` is the first block of output. -/
structure Xof where
  state : Keccak.Impl.State
  rate : Nat
  /-- No block has been read yet, so the state is not to be permuted before the next one. -/
  fresh : Bool

/-- Absorb `m` into a sponge of `rate` bytes of rate and pad it after the domain byte `d`. -/
def Xof.init (rate : Nat) (m : ByteArray) (d : UInt8 := 0x1f) : Xof :=
  let full := m.size / rate
  let s :=
    Keccak.Impl.run rate m 0
      ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ full
  let rest := m.size - rate * full
  let tail := m.extract (rate * full) m.size
  let tail :=
    if rest + 1 = rate then tail.push (d ||| 0x80)
    else (tail.push d ++ zeros (rate - rest - 2)).push 0x80
  ⟨Keccak.Impl.run rate tail 0 s 1, rate, true⟩

/-- The `n` lanes of the state as bytes, appended to `out`. -/
private def pushLanes (s : Keccak.Impl.State) (out : ByteArray) : Nat → Nat → ByteArray
  | _, 0 => out
  | i, n + 1 => pushLanes s (pushLe64 out (lane s i)) (i + 1) n

/-- The state whose first `rate` bytes are the next block of output (lane `i` holds bytes `8 i` to
`8 i + 7`, least significant first). -/
def Xof.next (x : Xof) : Keccak.Impl.State × Xof :=
  let s := if x.fresh then x.state else Keccak.Impl.permute x.state 24
  (s, ⟨s, x.rate, false⟩)

/-- The next `rate` bytes of output. -/
def Xof.block (x : Xof) : ByteArray × Xof :=
  let (s, x) := x.next
  (pushLanes s (ByteArray.emptyWithCapacity x.rate) 0 (x.rate / 8), x)

/-- The first `n` bytes of output, block by block. -/
private def squeezeAll (x : Xof) (out : ByteArray) : Nat → ByteArray
  | 0 => out
  | blocks + 1 =>
    let (b, x) := x.block
    squeezeAll x (out ++ b) blocks

/-- The sponge with the domain byte `d`, `rate` bytes of rate and `n` bytes of output. -/
def xof (d : UInt8) (rate : Nat) (m : ByteArray) (n : Nat) : ByteArray :=
  (squeezeAll (Xof.init rate m d) ByteArray.empty ((n + rate - 1) / rate)).extract 0 n

/-- SHAKE128. -/
def shake128 (m : ByteArray) (n : Nat) : ByteArray :=
  xof 0x1f 168 m n

/-- SHAKE256. -/
def shake256 (m : ByteArray) (n : Nat) : ByteArray :=
  xof 0x1f 136 m n

/-- SHA3-256. -/
def sha3_256 (m : ByteArray) : ByteArray :=
  xof 0x06 136 m 32

end Impl

end NearCrypto.Shake

namespace NearCrypto

/-- SHAKE128 with `n` bytes of output (FIPS 202). -/
def shake128 (m : ByteArray) (n : Nat) : ByteArray :=
  Shake.Impl.shake128 m n

/-- SHAKE256 with `n` bytes of output (FIPS 202). -/
def shake256 (m : ByteArray) (n : Nat) : ByteArray :=
  Shake.Impl.shake256 m n

/-- SHA3-256 (FIPS 202: the padding `0x06`, not Keccak's `0x01`). -/
def sha3_256 (m : ByteArray) : ByteArray :=
  Shake.Impl.sha3_256 m

end NearCrypto
