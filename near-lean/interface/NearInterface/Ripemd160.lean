import Lean

/-! Pure RIPEMD-160, as nearcore's `ripemd160` host computes it, written from
Dobbertin, Bosselaers and Preneel, "RIPEMD-160: A Strengthened Version of
RIPEMD" (1996). Arithmetic uses wrapping UInt32; this does not establish a
refinement to the specification. -/
namespace Near.Ripemd160

/-- Message word selection, left and right lines. -/
private def wordLeft : Array Nat := #[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13]

private def wordRight : Array Nat := #[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11]

/-- Rotation amounts, left and right lines. -/
private def shiftLeft : Array UInt32 := #[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6]

private def shiftRight : Array UInt32 := #[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11]

private def constLeft : Array UInt32 := #[0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]
private def constRight : Array UInt32 := #[0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

private def rotl (x n : UInt32) : UInt32 := if n == 0 then x else (x <<< n) ||| (x >>> (32 - n))

/-- The nonlinear function of round `j / 16`. -/
private def f (j : Nat) (x y z : UInt32) : UInt32 :=
  match j / 16 with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| (~~~x &&& z)
  | 2 => (x ||| ~~~y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | _ => x ^^^ (y ||| ~~~z)

/-- Process one 64-byte block. -/
private def compress (h : Array UInt32) (block : List UInt8) : Array UInt32 := Id.run do
  let words := (List.range 16).toArray.map fun i =>
    (List.range 4).foldl (fun w k => w ||| ((block[4 * i + k]!).toUInt32 <<< (8 * k).toUInt32)) 0
  let mut (al, bl, cl, dl, el) := (h[0]!, h[1]!, h[2]!, h[3]!, h[4]!)
  let mut (ar, br, cr, dr, er) := (h[0]!, h[1]!, h[2]!, h[3]!, h[4]!)
  for j in [0:80] do
    let t := rotl (al + f j bl cl dl + words[wordLeft[j]!]! + constLeft[j / 16]!) shiftLeft[j]! + el
    (al, el, dl, cl, bl) := (el, dl, rotl cl 10, bl, t)
    let t := rotl (ar + f (79 - j) br cr dr + words[wordRight[j]!]! + constRight[j / 16]!) shiftRight[j]! + er
    (ar, er, dr, cr, br) := (er, dr, rotl cr 10, br, t)
  return #[h[1]! + cl + dr, h[2]! + dl + er, h[3]! + el + ar, h[4]! + al + br, h[0]! + bl + cr]

/-- The 64-byte blocks of a padded message. -/
private def blocks (bytes : List UInt8) : List (List UInt8) :=
  (List.range (bytes.length / 64)).map fun i => (bytes.drop (i * 64)).take 64

def hash (input : List UInt8) : List UInt8 :=
  let bits := 8 * input.length
  let padding := [0x80] ++ List.replicate ((119 - input.length % 64) % 64) 0 ++
    (List.range 8).map fun i => UInt8.ofNat (bits / 2 ^ (8 * i) % 256)
  let h := (blocks (input ++ padding)).foldl compress
    #[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]
  h.toList.flatMap fun word => (List.range 4).map fun k => (word >>> (8 * k).toUInt32).toUInt8

end Near.Ripemd160
