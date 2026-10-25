/-!
# CRC-32

The IEEE 802.3 checksum (reflected polynomial `0xEDB88320`), table driven. It guards each log record
and the snapshot of the store against torn and corrupted writes.
-/

namespace Near.Node.Store

/-- The 256-entry table. -/
def crcTable : Array UInt32 :=
  (Array.range 256).map fun (n : Nat) =>
    Id.run do
      let mut c : UInt32 := n.toUInt32
      for _ in [0:8] do
        c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
      return c

/-- Continue a checksum (`crc32Update 0 d` is the checksum of `d`). -/
def crc32Update (crc : UInt32) (d : ByteArray) : UInt32 :=
  Id.run do
    let mut c := crc ^^^ (0xFFFFFFFF : UInt32)
    for b in d do
      c := crcTable[((c ^^^ b.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)
    return c ^^^ (0xFFFFFFFF : UInt32)

def crc32 (d : ByteArray) : UInt32 :=
  crc32Update 0 d

end Near.Node.Store
