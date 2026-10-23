import NearNode.Borsh.Spec
import NearNode.Borsh.Impl

/-!
# Borsh

`Codec α` pairs the reference codec (`Spec`) and the fast codec (`Impl`) of one
type. Types define it once, from the combinators below, so the two cannot
drift apart structurally. Structs are tuples of their fields (`iso`), enums are
tables of tagged variants (`enum`).
-/

namespace Near.Node.Borsh

/-- The Borsh format of `α`, as reference semantics and as fast path. -/
class Codec (α : Type) where
  spec : Spec.Codec α
  impl : Impl.Codec α

namespace Codec

/-- Encode with the fast path. -/
def encode [Codec α] (a : α) : ByteArray :=
  Codec.impl.put a ByteArray.empty

/-- Decode with the fast path, requiring that all input is consumed. -/
def decodeAll [Codec α] (d : ByteArray) : Except Error α :=
  (Codec.impl : Impl.Codec α).decodeAll d

/-- Encode with the reference semantics. -/
def encodeSpec [Codec α] (a : α) : List UInt8 :=
  Codec.spec.enc a

/-- Decode with the reference semantics, requiring that all input is consumed. -/
def decodeAllSpec [Codec α] (l : List UInt8) : Except Error α :=
  (Codec.spec : Spec.Codec α).decodeAll l

/-- Transport a codec along an isomorphism (a struct is a tuple of its fields). -/
@[instance_reducible]
def isoOf (c : Codec α) (f : α → β) (g : β → α) : Codec β :=
  ⟨Spec.imap c.spec f g, Impl.imap c.impl f g⟩

/-- Like `isoOf`, with a decoder that may reject. -/
@[instance_reducible]
def tryIsoOf (c : Codec α) (f : α → Except Error β) (g : β → α) : Codec β :=
  ⟨Spec.tryMap c.spec f g, Impl.tryMap c.impl f g⟩

/-- `isoOf` with the codec found by instance search. -/
@[instance_reducible]
def iso (α : Type) [c : Codec α] (f : α → β) (g : β → α) : Codec β :=
  isoOf c f g

instance : Codec UInt8 :=
  ⟨Spec.u8, Impl.u8⟩

instance : Codec UInt16 :=
  ⟨Spec.u16, Impl.u16⟩

instance : Codec UInt32 :=
  ⟨Spec.u32, Impl.u32⟩

instance : Codec UInt64 :=
  ⟨Spec.u64, Impl.u64⟩

instance : Codec U128 :=
  ⟨Spec.u128, Impl.u128⟩

instance : Codec Bool :=
  ⟨Spec.bool, Impl.bool⟩

instance : Codec Unit :=
  ⟨Spec.unit, Impl.unit⟩

/-- `Vec<u8>`. -/
instance : Codec ByteArray :=
  ⟨Spec.bytes, Impl.bytes⟩

instance : Codec String :=
  ⟨Spec.string, Impl.string⟩

instance [c : Codec α] : Codec (Array α) :=
  ⟨Spec.vec c.spec, Impl.vec c.impl⟩

instance [c : Codec α] : Codec (Option α) :=
  ⟨Spec.option c.spec, Impl.option c.impl⟩

instance [a : Codec α] [b : Codec β] : Codec (α × β) :=
  ⟨Spec.pair a.spec b.spec, Impl.pair a.impl b.impl⟩

/-- Concatenation of two explicit codecs. -/
@[instance_reducible]
def pair (a : Codec α) (b : Codec β) : Codec (α × β) :=
  ⟨Spec.pair a.spec b.spec, Impl.pair a.impl b.impl⟩

/-- `[u8; n]`. -/
@[instance_reducible]
def fixed (n : Nat) : Codec ByteArray :=
  ⟨Spec.fixed n, Impl.fixed n⟩

/-- A `BTreeMap`, as the array of its entries in ascending key order. -/
@[instance_reducible]
def btreeMap (cmp : K → K → Ordering) (k : Codec K) (v : Codec V) : Codec (Array (K × V)) :=
  ⟨Spec.btreeMap cmp k.spec v.spec, Impl.btreeMap cmp k.impl v.impl⟩

/-- One enum variant with its tag. -/
structure Case (α : Type) where
  spec : Spec.Case α
  impl : Impl.Case α

/-- A variant that carries a payload; `prj` returns it when the value is this variant. -/
def Case.variantOf (tag : UInt8) (c : Codec β) (inj : β → α) (prj : α → Option β) : Case α :=
  ⟨.variant tag c.spec inj prj, .variant tag c.impl inj prj⟩

/-- `variantOf` with the payload codec found by instance search. -/
def Case.variant (tag : UInt8) (β : Type) [c : Codec β] (inj : β → α) (prj : α → Option β) :
    Case α :=
  .variantOf tag c inj prj

/-- Reuse a variant of a sub-enum `β` inside an enum `α` that embeds it. -/
def Case.lift (c : Case β) (inj : β → α) (prj : α → Option β) : Case α where
  spec :=
    { tag := c.spec.tag
      enc := fun a => (prj a).bind c.spec.enc
      dec := fun l => (c.spec.dec l).map fun (b, r) => (inj b, r) }
  impl :=
    { tag := c.impl.tag
      applies := fun a => (prj a).any c.impl.applies
      put := fun a d =>
        match prj a with
        | some b => c.impl.put b d
        | none => d
      get := fun d p => (c.impl.get d p).map inj }

/-- A variant without payload. -/
def Case.const [BEq α] (tag : UInt8) (a : α) : Case α :=
  .variant tag Unit (fun _ => a) fun x => if x == a then some () else none

/-- An enum: a `u8` tag selects the variant, and tags outside the table are rejected. -/
@[instance_reducible]
def enum (what : String) (cases : List (Case α)) : Codec α :=
  ⟨Spec.enum what (cases.map (·.spec)), Impl.enum what (cases.map (·.impl))⟩

end Codec

/-- Compare byte strings lexicographically, like Rust's `Vec<u8>` order. -/
def compareBytes (a b : ByteArray) : Ordering :=
  let rec go (i : Nat) (fuel : Nat) : Ordering :=
    match fuel with
    | 0 => .eq
    | fuel + 1 =>
      if i < a.size && i < b.size then compare a[i]! b[i]! |>.then (go (i + 1) fuel)
      else compare a.size b.size
  go 0 (a.size + 1)

end Near.Node.Borsh
