import NearRuntime.Types

/-! Little-endian integers and a byte parser for the Borsh records of the shard machinery
(shard layout, congestion info, scheduler state, queue indices). Only what those records use. -/
namespace Near.Wire

/-- `width` little-endian bytes of `value`; the caller checks that the value fits. -/
def little (width value : Nat) : Bytes :=
  (List.range width).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

/-- The unsigned integer a little-endian byte string denotes. -/
def number (bytes : Bytes) : Nat := bytes.foldr (fun byte rest => byte.toNat + 256 * rest) 0

/-- `little` that fails when the value needs more than `width` bytes (`checked_add` overflow). -/
def unsigned (width value : Nat) : Except String Bytes := do
  unless value < 2 ^ (8 * width) do throw s!"integer exceeds u{8 * width}"
  return little width value

/-- A parser over the remaining bytes. -/
abbrev Parser := StateT Bytes (Except String)

def take (n : Nat) : Parser Bytes := do
  let rest ← get
  if rest.length < n then throw "truncated record"
  set (rest.drop n)
  return rest.take n

def uint (width : Nat) : Parser Nat := do return number (← take width)

def string : Parser String := do
  let bytes ← take (← uint 4)
  match String.fromUTF8? ⟨bytes.toArray⟩ with
  | some text => return text
  | none => throw "invalid UTF-8"

/-- `count` repetitions of `item`. -/
def repeatN (count : Nat) (item : Parser α) : Parser (List α) := do
  let mut found := []
  for _ in List.range count do
    found := found ++ [← item]
  return found

/-- Run a parser that must consume every byte. -/
def run (parser : Parser α) (bytes : Bytes) : Except String α := do
  let (value, rest) ← parser.run bytes
  unless rest.isEmpty do throw "trailing bytes"
  return value

end Near.Wire
