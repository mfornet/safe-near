/-!
# Zstandard decompression

RFC 8878: frames (and skippable frames), raw, RLE and compressed blocks, Huffman-coded literals
(one or four streams, FSE-compressed or direct weights, the previous table when "treeless"), FSE-coded
sequences (predefined, RLE, FSE-compressed and repeated tables) with the repeat offsets, and the optional
content checksum (XXH64). Dictionaries are rejected. nearcore compresses every state part with zstd
(`StatePartV1`), so a node that syncs state needs a decoder; the output of the `zstd` crate at levels
-5 to 22 is the test (`NodeConformance.Zstd`).

The decoder reads every length it is given and fails with a message instead of reading outside its
input; the output is bounded by the `limit` argument (nearcore's `PART_SIZE_LIMIT`, 512 MiB, for state
parts).
-/

namespace Near.Node.Zstd

/-! ### Bit readers -/

/-- Bits `[bit, bit + count)` of `data` (bit `i` is bit `i % 8` of byte `i / 8`) as a little-endian
number; bits past the end read as zero. -/
def bitsAt (data : ByteArray) (bit count : Nat) : Nat :=
  if count == 0 then 0
  else
    let lo := bit / 8
    let hi := (bit + count - 1) / 8
    let v :=
      Id.run do
        let mut v := 0
        for j in [0:hi - lo + 1] do
          v := v ||| ((data.get! (lo + j)).toNat <<< (8 * j))
        pure v
    (v >>> (bit % 8)) % (2 ^ count)

/-- A stream read from its end towards its start (Huffman and FSE data). `pos` is the number of
bits not read yet, counted from the start of the stream; `over` says that more bits were asked for
than the stream had (the missing ones read as zero). -/
structure Back where
  data : ByteArray
  pos : Nat
  over : Bool := false

/-- The stream in `data[start, stop)`: the last byte holds a marker bit (the highest bit set) after
the data. -/
def Back.init (data : ByteArray) (start stop : Nat) : Except String Back := do
  if stop ≤ start || stop > data.size then
    throw "empty bitstream"
  let last := (data.get! (stop - 1)).toNat
  if last == 0 then
    throw "bitstream without an end marker"
  let mut high := 0
  for i in [0:8] do
    if (last >>> i) % 2 == 1 then
      high := i
  pure { data := data.extract start stop, pos := (stop - 1 - start) * 8 + high }

/-- The next `n` bits as a number, the first one being the most significant. -/
def Back.peek (b : Back) (n : Nat) : Nat :=
  if n == 0 then 0
  else if b.pos ≥ n then bitsAt b.data (b.pos - n) n else bitsAt b.data 0 b.pos <<< (n - b.pos)

def Back.read (b : Back) (n : Nat) : Nat × Back :=
  let v := b.peek n
  if b.pos ≥ n then (v, { b with pos := b.pos - n })
  else
    (v,
      { b with
        pos := 0, over := true })

def Back.consume (b : Back) (n : Nat) : Back :=
  if b.pos ≥ n then { b with pos := b.pos - n }
  else
    { b with
      pos := 0, over := true }

/-! ### FSE -/

/-- A cell of a decoding table: the symbol, the bits to read for the next state, and its base. -/
structure Cell where
  symbol : Nat
  bits : Nat
  base : Nat
  deriving Inhabited

structure Fse where
  accLog : Nat
  cells : Array Cell
  deriving Inhabited

private def highBit (n : Nat) : Nat :=
  Nat.log2 n

/-- The decoding table of a normalized distribution (`-1` is a probability below one). -/
def Fse.build (norm : Array Int) (accLog : Nat) : Except String Fse := do
  let size := 1 <<< accLog
  let mut cells : Array Cell := Array.replicate size default
  let mut next : Array Nat := Array.replicate norm.size 0
  let mut high := size
  let mut total : Int := 0
  for s in [0:norm.size] do
    let c := norm[s]!
    total := total + (if c < 0 then 1 else c)
    if c == -1 then
      high := high - 1
      cells := cells.set! high { symbol := s, bits := 0, base := 0 }
      next := next.set! s 1
    else if c > 0 then
      next := next.set! s c.toNat
  if total != size then
    throw s!"FSE distribution {norm} sums to {total}, not {size}"
  let step := (size >>> 1) + (size >>> 3) + 3
  let mask := size - 1
  let mut position := 0
  for s in [0:norm.size] do
    let c := norm[s]!
    if c > 0 then
      for _ in [0:c.toNat] do
        cells := cells.set! position { symbol := s, bits := 0, base := 0 }
        position := (position + step) &&& mask
        while position ≥ high do
          position := (position + step) &&& mask
  if position != 0 then
    throw "FSE table spread does not return to the start"
  for u in [0:size] do
    let s := cells[u]!.symbol
    let n := next[s]!
    next := next.set! s (n + 1)
    let bits := accLog - highBit n
    cells := cells.set! u { symbol := s, bits, base := (n <<< bits) - size }
  pure { accLog, cells }

/-- A table with one symbol (`RLE` mode). -/
def Fse.single (symbol : Nat) : Fse :=
  { accLog := 0, cells := #[{ symbol, bits := 0, base := 0 }] }

/-- The distribution at the start of `data[start, stop)` and the number of bytes it took
(`FSE_readNCount`). -/
def readDistribution (data : ByteArray) (start stop : Nat) (maxSymbol maxLog : Nat) :
    Except String (Array Int × Nat × Nat) := do
  let avail := (stop - start) * 8
  let mut bit := 0
  let read (bit n : Nat) : Except String Nat := do
    if bit + n > avail then
      throw "truncated FSE table description"
    pure (bitsAt data (start * 8 + bit) n)
  let accLog := 5 + (← read bit 4)
  bit := bit + 4
  if accLog > maxLog then
    throw "FSE accuracy log too large"
  let mut remaining : Int := (1 <<< accLog) + 1
  let mut threshold : Nat := 1 <<< accLog
  let mut nbBits := accLog + 1
  let mut norm : Array Int := #[]
  let mut previousZero := false
  while remaining > 1 && norm.size ≤ maxSymbol do
    if previousZero then
      let mut run := 0
      repeat
        let r ← read bit 2
        bit := bit + 2
        run := run + r
        if r != 3 then
          break
      for _ in [0:run] do
        norm := norm.push 0
      if norm.size > maxSymbol + 1 then
        throw "FSE distribution has too many symbols"
    if norm.size > maxSymbol then
      break
    let max : Int := (2 * threshold - 1) - remaining
    let low ← read bit (nbBits - 1)
    let count : Int ←
      if (low : Int) < max then
        bit := bit + nbBits - 1
        pure low
      else
        let all ← read bit nbBits
        bit := bit + nbBits
        let c := all % (2 * threshold)
        pure (if c ≥ threshold then (c : Int) - max else c)
    let count := count - 1
    remaining := remaining - (if count < 0 then -count else count)
    norm := norm.push count
    previousZero := count == 0
    while remaining < threshold && threshold > 1 do
      nbBits := nbBits - 1
      threshold := threshold >>> 1
  if remaining != 1 then
    throw "FSE distribution does not sum to its table size"
  if norm.size > maxSymbol + 1 then
    throw "FSE distribution has too many symbols"
  pure (norm, accLog, (bit + 7) / 8)

/-! ### Huffman -/

structure Huff where
  maxBits : Nat
  /-- Indexed by the next `maxBits` bits: the symbol and the bits it uses. -/
  cells : Array (Nat × Nat)
  deriving Inhabited

/-- The decoding table of the weights of symbols `0 .. weights.size` (the last weight is implied). -/
def Huff.build (explicit : Array Nat) : Except String Huff := do
  let mut sum := 0
  for w in explicit do
    if w > 11 then
      throw "Huffman weight too large"
    if w > 0 then
      sum := sum + (1 <<< (w - 1))
  if sum == 0 then
    throw "Huffman tree without symbols"
  let maxBits := Nat.log2 sum + 1
  if maxBits > 11 then
    throw "Huffman code too long"
  let left := (1 <<< maxBits) - sum
  if left == 0 || (left &&& (left - 1)) != 0 then
    throw "Huffman weights do not complete a prefix code"
  let last := Nat.log2 left + 1
  let weights := explicit.push last
  if weights.size > 256 then
    throw "Huffman tree with more than 256 symbols"
  let size := 1 <<< maxBits
  let mut start : Array Nat := Array.replicate (maxBits + 2) 0
  let mut counts : Array Nat := Array.replicate (maxBits + 2) 0
  for w in weights do
    if w > maxBits then
      throw "Huffman weight above the code length"
    counts := counts.set! w (counts[w]! + 1)
  let mut acc := 0
  for w in [1:maxBits + 1] do
    start := start.set! w acc
    acc := acc + counts[w]! * (1 <<< (w - 1))
  if acc != size then
    throw "Huffman table does not fill its size"
  let mut cells : Array (Nat × Nat) := Array.replicate size (0, 0)
  for s in [0:weights.size] do
    let w := weights[s]!
    if w > 0 then
      let len := 1 <<< (w - 1)
      let from_ := start[w]!
      for i in [0:len] do
        cells := cells.set! (from_ + i) (s, maxBits + 1 - w)
      start := start.set! w (from_ + len)
  pure { maxBits, cells }

/-- `count` symbols from the stream (the stream must not run out). -/
def Huff.decode (h : Huff) (data : ByteArray) (start stop : Nat) (count : Nat) :
    Except String ByteArray := do
  let mut b ← Back.init data start stop
  let mut out := ByteArray.empty
  for _ in [0:count] do
    let (s, n) := h.cells[b.peek h.maxBits]!
    b := b.consume n
    out := out.push s.toUInt8
  if b.over then
    throw "Huffman stream ended early"
  pure out

/-- The Huffman tree description at `data[start, ..)`: the table and the offset after it. -/
def readHuffmanTree (data : ByteArray) (start stop : Nat) : Except String (Huff × Nat) := do
  if start ≥ stop then
    throw "truncated Huffman tree"
  let header := (data.get! start).toNat
  if header ≥ 128 then
    let n := header - 127
    let bytes := (n + 1) / 2
    if start + 1 + bytes > stop then
      throw "truncated Huffman weights"
    let mut weights : Array Nat := #[]
    for i in [0:n] do
      let byte := (data.get! (start + 1 + i / 2)).toNat
      weights := weights.push (if i % 2 == 0 then byte >>> 4 else byte &&& 15)
    pure (← Huff.build weights, start + 1 + bytes)
  else
    let size := header
    if size == 0 || start + 1 + size > stop then
      throw "truncated compressed Huffman weights"
    let end_ := start + 1 + size
    let (norm, accLog, used) ← readDistribution data (start + 1) end_ 255 6
    let table ← Fse.build norm accLog
    let mut b ← Back.init data (start + 1 + used) end_
    let mut s1 := (b.read accLog).1
    b := (b.read accLog).2
    let mut s2 := (b.read accLog).1
    b := (b.read accLog).2
    let mut weights : Array Nat := #[]
    -- two interleaved states; a symbol is taken before the state's update, and the other state's
    -- symbol ends the stream when an update ran past the data
    repeat
      if weights.size > 255 then
        throw "too many Huffman weights"
      let c1 := table.cells[s1]!
      weights := weights.push c1.symbol
      let (v, b') := b.read c1.bits
      b := b'
      s1 := c1.base + v
      if b.over then
        weights := weights.push table.cells[s2]!.symbol
        break
      if weights.size > 255 then
        throw "too many Huffman weights"
      let c2 := table.cells[s2]!
      weights := weights.push c2.symbol
      let (v, b') := b.read c2.bits
      b := b'
      s2 := c2.base + v
      if b.over then
        weights := weights.push table.cells[s1]!.symbol
        break
    pure (← Huff.build weights, end_)

/-! ### Sequences -/

private def llBase : Array Nat :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 20, 22, 24, 28, 32, 40, 48, 64,
    128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]

private def llBits : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10, 11,
    12, 13, 14, 15, 16]

private def mlBase : Array Nat :=
  #[3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
    29, 30, 31, 32, 33, 34, 35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051,
    4099, 8195, 16387, 32771, 65539]

private def mlBits : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]

private def llDefault : Array Int :=
  #[4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1,
    -1, -1, -1, -1]

private def ofDefault : Array Int :=
  #[1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1]

private def mlDefault : Array Int :=
  #[1, 4, 3, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, -1, -1]

/-- What a block remembers for the next one: the Huffman table, the three sequence tables and the
repeat offsets. -/
structure Tables where
  huff : Option Huff := none
  ll : Option Fse := none
  of_ : Option Fse := none
  ml : Option Fse := none
  /-- The three most recent offsets (they carry over from block to block). -/
  rep1 : Nat := 1
  rep2 : Nat := 4
  rep3 : Nat := 8

/-- One sequence table by its mode; returns the table and the offset after its description. -/
private def readTable (mode : Nat) (data : ByteArray) (pos stop : Nat) (maxSymbol maxLog : Nat)
    (default_ : Array Int) (defaultLog : Nat) (previous : Option Fse) : Except String (Fse × Nat) :=
  do
  match mode with
  | 0 =>
    pure (← Fse.build default_ defaultLog, pos)
  | 1 =>
    if pos ≥ stop then
      throw "truncated RLE sequence table"
    let s := (data.get! pos).toNat
    if s > maxSymbol then
      throw "RLE symbol out of range"
    pure (Fse.single s, pos + 1)
  | 2 =>
    let (norm, accLog, used) ← readDistribution data pos stop maxSymbol maxLog
    pure (← Fse.build norm accLog, pos + used)
  | _ =>
    match previous with
    | some t =>
      pure (t, pos)
    | none =>
      throw "repeated sequence table without a previous one"

/-! ### Blocks -/

/-- Decodes one compressed block, appending to `out`. -/
private def block (data : ByteArray) (start stop : Nat) (out : ByteArray) (floor : Nat)
    (tables : Tables) (limit : Nat) : Except String (ByteArray × Tables) := do
  let mut tables := tables
  let mut pos := start
  if pos ≥ stop then
    throw "empty compressed block"
  -- literals
  let b0 := (data.get! pos).toNat
  let litType := b0 &&& 3
  let sizeFormat := (b0 >>> 2) &&& 3
  let mut literals := ByteArray.empty
  if litType < 2 then
    let (regenerated, headerLen) ←
      match sizeFormat with
      | 0 | 2 =>
        pure (b0 >>> 3, 1)
      | 1 =>
        if pos + 2 > stop then
          throw "truncated literals header"
        pure ((b0 >>> 4) ||| ((data.get! (pos + 1)).toNat <<< 4), 2)
      | _ =>
        if pos + 3 > stop then
          throw "truncated literals header"
        pure
            ((b0 >>> 4) ||| ((data.get! (pos + 1)).toNat <<< 4) |||
                ((data.get! (pos + 2)).toNat <<< 12),
              3)
    pos := pos + headerLen
    if regenerated > 131072 then
      throw "literals block too large"
    if litType == 0 then
      if pos + regenerated > stop then
        throw "truncated raw literals"
      literals := data.extract pos (pos + regenerated)
      pos := pos + regenerated
    else
      if pos + 1 > stop then
        throw "truncated RLE literals"
      literals := ByteArray.mk (Array.replicate regenerated (data.get! pos))
      pos := pos + 1
  else
    let (streams, regenerated, compressed, headerLen) ←
      match sizeFormat with
      | 0 | 1 =>
        if pos + 3 > stop then
          throw "truncated literals header"
        let v := b0 ||| ((data.get! (pos + 1)).toNat <<< 8) ||| ((data.get! (pos + 2)).toNat <<< 16)
        pure (if sizeFormat == 0 then 1 else 4, (v >>> 4) &&& 1023, (v >>> 14) &&& 1023, 3)
      | 2 =>
        if pos + 4 > stop then
          throw "truncated literals header"
        let v :=
          b0 ||| ((data.get! (pos + 1)).toNat <<< 8) ||| ((data.get! (pos + 2)).toNat <<< 16) |||
            ((data.get! (pos + 3)).toNat <<< 24)
        pure (4, (v >>> 4) &&& 16383, (v >>> 18) &&& 16383, 4)
      | _ =>
        if pos + 5 > stop then
          throw "truncated literals header"
        let v :=
          b0 ||| ((data.get! (pos + 1)).toNat <<< 8) ||| ((data.get! (pos + 2)).toNat <<< 16) |||
            ((data.get! (pos + 3)).toNat <<< 24) |||
            ((data.get! (pos + 4)).toNat <<< 32)
        pure (4, (v >>> 4) &&& 262143, (v >>> 22) &&& 262143, 5)
    pos := pos + headerLen
    if regenerated > 131072 then
      throw "literals block too large"
    let end_ := pos + compressed
    if end_ > stop then
      throw "truncated compressed literals"
    let huff ←
      if litType == 2 then
        let (h, after) ← readHuffmanTree data pos end_
        pos := after
        tables := { tables with huff := some h }
        pure h
      else
        match tables.huff with
        | some h =>
          pure h
        | none =>
          throw "treeless literals without a previous Huffman table"
    if streams == 1 then
      literals ← huff.decode data pos end_ regenerated
    else
      if pos + 6 > end_ then
        throw "truncated jump table"
      let size (i : Nat) : Nat :=
        (data.get! (pos + 2 * i)).toNat ||| ((data.get! (pos + 2 * i + 1)).toNat <<< 8)
      let s1 := size 0
      let s2 := size 1
      let s3 := size 2
      let a := pos + 6
      let b := a + s1
      let c := b + s2
      let d := c + s3
      if d > end_ then
        throw "Huffman streams longer than the section"
      let per := (regenerated + 3) / 4
      if 3 * per > regenerated then
        throw "literals too short for four streams"
      literals :=
        (← huff.decode data a b per) ++ (← huff.decode data b c per) ++
          (← huff.decode data c d per) ++
          (← huff.decode data d end_ (regenerated - 3 * per))
    pos := end_
  -- sequences
  let mut out := out
  if pos ≥ stop then
    throw "missing sequences section"
  let n0 := (data.get! pos).toNat
  let (count, afterCount) ←
    if n0 == 0 then
      pure (0, pos + 1)
    else if n0 < 128 then
      pure (n0, pos + 1)
    else if n0 < 255 then
      if pos + 2 > stop then
        throw "truncated sequence count"
      pure (((n0 - 128) <<< 8) + (data.get! (pos + 1)).toNat, pos + 2)
    else
      if pos + 3 > stop then
        throw "truncated sequence count"
      pure ((data.get! (pos + 1)).toNat + ((data.get! (pos + 2)).toNat <<< 8) + 0x7F00, pos + 3)
  pos := afterCount
  if count == 0 then
    if pos != stop then
      throw "bytes after a block without sequences"
    out := out ++ literals
    if out.size > limit then
      throw "output too large"
    return (out, tables)
  if pos ≥ stop then
    throw "missing symbol compression modes"
  let modes := (data.get! pos).toNat
  pos := pos + 1
  if modes &&& 3 != 0 then
    throw "reserved bits of the symbol compression modes"
  let (llTable, p1) ← readTable (modes >>> 6) data pos stop 35 9 llDefault 6 tables.ll
  let (ofTable, p2) ← readTable ((modes >>> 4) &&& 3) data p1 stop 31 8 ofDefault 5 tables.of_
  let (mlTable, p3) ← readTable ((modes >>> 2) &&& 3) data p2 stop 52 9 mlDefault 6 tables.ml
  tables :=
    { tables with
      ll := some llTable, of_ := some ofTable, ml := some mlTable }
  let mut bits ← Back.init data p3 stop
  let (s, b') := bits.read llTable.accLog
  let mut llState := s
  bits := b'
  let (s, b') := bits.read ofTable.accLog
  let mut ofState := s
  bits := b'
  let (s, b') := bits.read mlTable.accLog
  let mut mlState := s
  bits := b'
  let mut rep1 := tables.rep1
  let mut rep2 := tables.rep2
  let mut rep3 := tables.rep3
  let mut litPos := 0
  for i in [0:count] do
    let llCell := llTable.cells[llState]!
    let ofCell := ofTable.cells[ofState]!
    let mlCell := mlTable.cells[mlState]!
    let ofCode := ofCell.symbol
    let mlCode := mlCell.symbol
    let llCode := llCell.symbol
    if ofCode > 31 then
      throw "offset code out of range"
    let (extra, b') := bits.read ofCode
    bits := b'
    let offsetValue := (1 <<< ofCode) + extra
    let (extra, b') := bits.read mlBits[mlCode]!
    bits := b'
    let matchLength := mlBase[mlCode]! + extra
    let (extra, b') := bits.read llBits[llCode]!
    bits := b'
    let literalLength := llBase[llCode]! + extra
    -- the offset and the repeat offsets
    let mut offset := 0
    if offsetValue > 3 then
      offset := offsetValue - 3
      rep3 := rep2
      rep2 := rep1
      rep1 := offset
    else if literalLength != 0 then
      if offsetValue == 1 then
        offset := rep1
      else if offsetValue == 2 then
        offset := rep2
        rep2 := rep1
        rep1 := offset
      else
        offset := rep3
        rep3 := rep2
        rep2 := rep1
        rep1 := offset
    else
      if offsetValue == 1 then
        offset := rep2
        rep2 := rep1
        rep1 := offset
      else if offsetValue == 2 then
        offset := rep3
        rep3 := rep2
        rep2 := rep1
        rep1 := offset
      else
        offset := rep1 - 1
        rep3 := rep2
        rep2 := rep1
        rep1 := offset
    if offset == 0 then
      throw "zero offset"
    if litPos + literalLength > literals.size then
      throw "sequence reads past the literals"
    out := out ++ literals.extract litPos (litPos + literalLength)
    litPos := litPos + literalLength
    if offset > out.size - floor then
      throw "match offset before the start of the frame"
    if out.size + matchLength > limit then
      throw "output too large"
    for _ in [0:matchLength] do
      out := out.push (out.get! (out.size - offset))
    if i + 1 < count then
      let (v, b') := bits.read llCell.bits
      bits := b'
      llState := llCell.base + v
      let (v, b') := bits.read mlCell.bits
      bits := b'
      mlState := mlCell.base + v
      let (v, b') := bits.read ofCell.bits
      bits := b'
      ofState := ofCell.base + v
  if bits.over || bits.pos != 0 then
    throw "sequence bitstream not fully consumed"
  out := out ++ literals.extract litPos literals.size
  if out.size > limit then
    throw "output too large"
  pure
      (out,
        { tables with
          rep1, rep2, rep3 })

/-! ### XXH64 -/

private def prime1 : UInt64 :=
  11400714785074694791

private def prime2 : UInt64 :=
  14029467366897019727

private def prime3 : UInt64 :=
  1609587929392839161

private def prime4 : UInt64 :=
  9650029242287828579

private def prime5 : UInt64 :=
  2870177450012600261

private def rotl (x : UInt64) (r : UInt64) : UInt64 :=
  (x <<< r) ||| (x >>> (64 - r))

private def le64 (d : ByteArray) (o : Nat) : UInt64 :=
  (List.range 8).foldl (fun a i => a ||| ((d.get! (o + i)).toUInt64 <<< (8 * i).toUInt64)) 0

private def le32 (d : ByteArray) (o : Nat) : UInt64 :=
  (List.range 4).foldl (fun a i => a ||| ((d.get! (o + i)).toUInt64 <<< (8 * i).toUInt64)) 0

private def xround (acc input : UInt64) : UInt64 :=
  rotl (acc + input * prime2) 31 * prime1

private def mergeRound (acc v : UInt64) : UInt64 :=
  (acc ^^^ xround 0 v) * prime1 + prime4

/-- XXH64 with seed 0. -/
def xxh64 (d : ByteArray) : UInt64 :=
  Id.run do
    let len := d.size
    let mut pos := 0
    let mut h : UInt64 := 0
    if len ≥ 32 then
      let mut v1 := prime1 + prime2
      let mut v2 := prime2
      let mut v3 : UInt64 := 0
      let mut v4 := 0 - prime1
      while pos + 32 ≤ len do
        v1 := xround v1 (le64 d pos)
        v2 := xround v2 (le64 d (pos + 8))
        v3 := xround v3 (le64 d (pos + 16))
        v4 := xround v4 (le64 d (pos + 24))
        pos := pos + 32
      h := rotl v1 1 + rotl v2 7 + rotl v3 12 + rotl v4 18
      h := mergeRound h v1
      h := mergeRound h v2
      h := mergeRound h v3
      h := mergeRound h v4
    else
      h := prime5
    h := h + len.toUInt64
    while pos + 8 ≤ len do
      h := h ^^^ xround 0 (le64 d pos)
      h := rotl h 27 * prime1 + prime4
      pos := pos + 8
    if pos + 4 ≤ len then
      h := h ^^^ (le32 d pos * prime1)
      h := rotl h 23 * prime2 + prime3
      pos := pos + 4
    while pos < len do
      h := h ^^^ ((d.get! pos).toUInt64 * prime5)
      h := rotl h 11 * prime1
      pos := pos + 1
    h := h ^^^ (h >>> 33)
    h := h * prime2
    h := h ^^^ (h >>> 29)
    h := h * prime3
    h := h ^^^ (h >>> 32)
    return h

/-! ### Frames -/

/-- Decompresses all the frames of `data`. `limit` bounds the output. -/
def decompress (data : ByteArray) (limit : Nat) : Except String ByteArray := do
  let mut pos := 0
  let mut out := ByteArray.empty
  let mut frames := 0
  while pos < data.size do
    if pos + 4 > data.size then
      throw "truncated frame magic"
    let magic := le32 data pos
    pos := pos + 4
    if magic &&& 0xFFFFFFF0 == 0x184D2A50 then
      if pos + 4 > data.size then
        throw "truncated skippable frame"
      let size := (le32 data pos).toNat
      pos := pos + 4
      if pos + size > data.size then
        throw "truncated skippable frame"
      pos := pos + size
      continue
    if magic != 0xFD2FB528 then
      throw "not a zstd frame"
    frames := frames + 1
    if pos ≥ data.size then
      throw "truncated frame header"
    let fhd := (data.get! pos).toNat
    pos := pos + 1
    if fhd &&& 8 != 0 then
      throw "reserved bit of the frame header"
    let single := (fhd >>> 5) &&& 1 == 1
    let checksum := (fhd >>> 2) &&& 1 == 1
    let sizeFlag := fhd >>> 6
    let dictFlag := fhd &&& 3
    if !single then
      if pos ≥ data.size then
        throw "truncated frame header"
      pos := pos + 1
    let dictBytes := #[0, 1, 2, 4][dictFlag]!
    if pos + dictBytes > data.size then
      throw "truncated frame header"
    let mut dict := 0
    for i in [0:dictBytes] do
      dict := dict ||| ((data.get! (pos + i)).toNat <<< (8 * i))
    if dict != 0 then
      throw "dictionaries are not supported"
    pos := pos + dictBytes
    let contentBytes :=
      if sizeFlag == 0 then (if single then 1 else 0) else #[0, 2, 4, 8][sizeFlag]!
    if pos + contentBytes > data.size then
      throw "truncated frame header"
    let mut content : Option Nat := none
    if contentBytes > 0 then
      let mut v := 0
      for i in [0:contentBytes] do
        v := v ||| ((data.get! (pos + i)).toNat <<< (8 * i))
      content := some (if sizeFlag == 1 then v + 256 else v)
    pos := pos + contentBytes
    let frameStart := out.size
    let mut tables : Tables := {}
    let mut last := false
    while !last do
      if pos + 3 > data.size then
        throw "truncated block header"
      let h :=
        (data.get! pos).toNat ||| ((data.get! (pos + 1)).toNat <<< 8) |||
          ((data.get! (pos + 2)).toNat <<< 16)
      pos := pos + 3
      last := h &&& 1 == 1
      let type := (h >>> 1) &&& 3
      let size := h >>> 3
      if type == 3 then
        throw "reserved block type"
      if type == 1 then
        if pos + 1 > data.size then
          throw "truncated RLE block"
        if out.size + size > limit then
          throw "output too large"
        out := out ++ ByteArray.mk (Array.replicate size (data.get! pos))
        pos := pos + 1
      else
        if pos + size > data.size then
          throw "truncated block"
        if type == 0 then
          if out.size + size > limit then
            throw "output too large"
          out := out ++ data.extract pos (pos + size)
        else
          let (o, t) ← block data pos (pos + size) out frameStart tables limit
          out := o
          tables := t
        pos := pos + size
    if let some n := content then
      if out.size - frameStart != n then
        throw "frame content size mismatch"
    if checksum then
      if pos + 4 > data.size then
        throw "truncated content checksum"
      let want := le32 data pos
      pos := pos + 4
      let got := xxh64 (out.extract frameStart out.size) &&& 0xFFFFFFFF
      if got != want then
        throw "content checksum mismatch"
  if frames == 0 then
    throw "no zstd frame"
  pure out

end Near.Node.Zstd
