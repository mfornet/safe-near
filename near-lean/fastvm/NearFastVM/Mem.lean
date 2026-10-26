import Wasm.Memory
import Wasm.Value

/-!
# Linear memory for the fast engine

The engine keeps the pages of the contract's memory in a plain `Array ByteArray` (the same representation as
`Wasm.Memory.pages`, so memory goes to and from the host functions without a copy) and reads and writes a
whole access at once instead of byte by byte through `List.range`.

Untouched pages are empty `ByteArray`s and read as zeros, as in `Wasm.Memory`. A write materialises its page
(`Wasm.Memory.write8` does the same), so the pages after a run have the shape the specification produces.
Bounds are checked by the caller against `pages.size * 65536`.
-/

namespace NearFastVM

open Wasm

/-- A page of zeros, built once: copying it is a `memcpy`, building it byte by byte is not. -/
def zeroPage : ByteArray :=
  Id.run do
    let mut page := ByteArray.mk #[0]
    for _ in [0:16] do
      page := page ++ page
    return page

/-- A fresh (unshared) page of zeros. -/
@[inline]
def newPage : ByteArray :=
  zeroPage.extract 0 pageSize

/-- The page, materialised if it was untouched. -/
@[inline]
def materialise (page : ByteArray) : ByteArray :=
  if page.size == 0 then newPage else page

@[inline]
def getByte (page : ByteArray) (o : Nat) : UInt64 :=
  if page.size == 0 then 0 else (page.get! o).toUInt64

/-- Read `n` (1, 2, 4 or 8) bytes at `ea`, little endian, where the access crosses no page boundary. -/
@[inline]
def readIn (page : ByteArray) (o : Nat) (n : Nat) : UInt64 :=
  if page.size == 0 then 0
  else
    if n == 1 then (page.get! o).toUInt64
    else
      if n == 2 then (page.get! o).toUInt64 ||| ((page.get! (o + 1)).toUInt64 <<< 8)
      else
        if n == 4 then
          (page.get! o).toUInt64 ||| ((page.get! (o + 1)).toUInt64 <<< 8) |||
            ((page.get! (o + 2)).toUInt64 <<< 16) |||
            ((page.get! (o + 3)).toUInt64 <<< 24)
        else
          (page.get! o).toUInt64 ||| ((page.get! (o + 1)).toUInt64 <<< 8) |||
            ((page.get! (o + 2)).toUInt64 <<< 16) |||
            ((page.get! (o + 3)).toUInt64 <<< 24) |||
            ((page.get! (o + 4)).toUInt64 <<< 32) |||
            ((page.get! (o + 5)).toUInt64 <<< 40) |||
            ((page.get! (o + 6)).toUInt64 <<< 48) |||
            ((page.get! (o + 7)).toUInt64 <<< 56)

/-- Byte at an address already known to be in bounds. -/
@[inline]
def readByte (pg : Array ByteArray) (ea : UInt64) : UInt64 :=
  getByte pg[(ea >>> 16).toNat]! (ea &&& 0xFFFF).toNat

/-- Read `n` bytes (1, 2, 4 or 8) at `ea`, which is in bounds. -/
def readN (pg : Array ByteArray) (ea : UInt64) (n : Nat) : UInt64 :=
  let o := (ea &&& 0xFFFF).toNat
  if o + n ≤ 65536 then readIn pg[(ea >>> 16).toNat]! o n
  else
    Id.run do
      let mut v : UInt64 := 0
      for k in [0:n] do
        v := v ||| (readByte pg (ea + k.toUInt64) <<< (8 * k).toUInt64)
      return v

@[inline]
def writeIn (page : ByteArray) (o : Nat) (n : Nat) (v : UInt64) : ByteArray :=
  let page := materialise page
  if n == 1 then page.set! o v.toUInt8
  else
    if n == 2 then (page.set! o v.toUInt8).set! (o + 1) (v >>> 8).toUInt8
    else
      if n == 4 then
        (((page.set! o v.toUInt8).set! (o + 1) (v >>> 8).toUInt8).set! (o + 2)
              (v >>> 16).toUInt8).set!
          (o + 3) (v >>> 24).toUInt8
      else
        (((((((page.set! o v.toUInt8).set! (o + 1) (v >>> 8).toUInt8).set! (o + 2)
                              (v >>> 16).toUInt8).set!
                          (o + 3) (v >>> 24).toUInt8).set!
                      (o + 4) (v >>> 32).toUInt8).set!
                  (o + 5) (v >>> 40).toUInt8).set!
              (o + 6) (v >>> 48).toUInt8).set!
          (o + 7) (v >>> 56).toUInt8

/-- Write the low `n` bytes (1, 2, 4 or 8) of `v` at `ea`, which is in bounds. -/
def writeN (pg : Array ByteArray) (ea : UInt64) (n : Nat) (v : UInt64) : Array ByteArray :=
  let o := (ea &&& 0xFFFF).toNat
  if o + n ≤ 65536 then pg.modify (ea >>> 16).toNat fun page => writeIn page o n v
  else
    Id.run do
      let mut pg := pg
      for k in [0:n] do
        let a := ea + k.toUInt64
        pg :=
          pg.modify (a >>> 16).toNat fun page =>
            writeIn page (a &&& 0xFFFF).toNat 1 (v >>> (8 * k).toUInt64)
      return pg

/-- `len` bytes (at most one page) of `b`. -/
private def run (b : UInt8) (len : Nat) : ByteArray :=
  if b == 0 then zeroPage.extract 0 len else ByteArray.mk (Array.replicate len b)

/-- `memory.fill`: `n` bytes of `b` from `d`, both in bounds. -/
def fill (pg : Array ByteArray) (d n : Nat) (b : UInt8) : Array ByteArray :=
  Id.run do
    let mut pg := pg
    let mut d := d
    let mut n := n
    while n > 0 do
      let o := d % pageSize
      let len := min n (pageSize - o)
      let chunk := run b len
      pg := pg.modify (d / pageSize) fun page => chunk.copySlice 0 (materialise page) o len
      d := d + len
      n := n - len
    return pg

/-- `len` bytes of a page from `o`, as a fresh array: an untouched page reads as zeros. -/
private def slice (page : ByteArray) (o len : Nat) : ByteArray :=
  if page.size == 0 then zeroPage.extract 0 len else page.extract o (o + len)

/-- `memory.copy` with `memmove` semantics: `n` bytes from `s` to `d`, both ranges in bounds. Each chunk
lies in one source page and one destination page and is read before it is written. -/
def copy (pg : Array ByteArray) (d s n : Nat) : Array ByteArray :=
  Id.run do
    let mut pg := pg
    if d ≤ s then
      let mut d := d
      let mut s := s
      let mut n := n
      while n > 0 do
        let so := s % pageSize
        let dO := d % pageSize
        let len := min n (min (pageSize - so) (pageSize - dO))
        let chunk := slice pg[s / pageSize]! so len
        pg := pg.modify (d / pageSize) fun page => chunk.copySlice 0 (materialise page) dO len
        d := d + len
        s := s + len
        n := n - len
    else
      let mut n := n
      while n > 0 do
        let sEnd := s + n
        let dEnd := d + n
        let sl := if sEnd % pageSize == 0 then pageSize else sEnd % pageSize
        let dl := if dEnd % pageSize == 0 then pageSize else dEnd % pageSize
        let len := min n (min sl dl)
        let so := sEnd - len
        let dO := dEnd - len
        let chunk := slice pg[so / pageSize]! (so % pageSize) len
        pg :=
          pg.modify (dO / pageSize) fun page =>
            chunk.copySlice 0 (materialise page) (dO % pageSize) len
        n := n - len
    return pg

end NearFastVM
