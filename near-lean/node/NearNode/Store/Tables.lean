import Std.Data.HashMap
import NearNode.Store.Format

/-!
# The in-memory tables

The content of every column: plain columns map a key to a value, the reference counted `State`
column maps a key to its data and a signed count. An entry whose count reaches zero is removed; a
negative count (a reference removed before its node was added, which nearcore tolerates until the
column is compacted) is kept and reads as absent.
-/

namespace Near.Node.Store

structure Tables where
  plain : Array (Std.HashMap ByteArray ByteArray) := Array.replicate 16 {}
  rc : Std.HashMap ByteArray (ByteArray × Int) := {}

namespace Tables

/-- The operations a column accepts: `rcAdd` on a reference counted column, `set` on the others;
`delete` on either. -/
def Op.valid : Op → Bool
  | .set c _ _ => !c.isRc
  | .delete _ _ => true
  | .rcAdd c _ _ _ => c.isRc

def apply (t : Tables) : Op → Tables
  | .set c k v => { t with plain := t.plain.modify c.id.toNat (·.insert k v) }
  | .delete c k =>
    if c.isRc then { t with rc := t.rc.erase k }
    else { t with plain := t.plain.modify c.id.toNat (·.erase k) }
  | .rcAdd _ k data delta =>
    match t.rc.get? k with
    | none => if delta == 0 then t else { t with rc := t.rc.insert k (data, delta) }
    | some (old, n) =>
      let m := n + delta
      if m == 0 then { t with rc := t.rc.erase k }
      else { t with rc := t.rc.insert k ((if data.isEmpty then old else data), m) }

/-- The value in a column. A reference counted entry reads as absent unless its count is positive. -/
def get (t : Tables) (c : Col) (k : ByteArray) : Option ByteArray :=
  if c.isRc then (t.rc.get? k).bind fun (d, n) => if n > 0 then some d else none
  else t.plain[c.id.toNat]!.get? k

/-- The count of a reference counted entry. -/
def refcount (t : Tables) (k : ByteArray) : Int :=
  ((t.rc.get? k).map (·.2)).getD 0

/-- The number of entries in a column. -/
def size (t : Tables) (c : Col) : Nat :=
  if c.isRc then t.rc.size else t.plain[c.id.toNat]!.size

/-- Same content. -/
def equal (a b : Tables) : Bool :=
  let sameMap (x y : Std.HashMap ByteArray ByteArray) :=
    x.size == y.size && x.fold (fun ok k v => ok && y.get? k == some v) true
  (a.plain.size == b.plain.size) &&
    (List.range a.plain.size).all (fun i => sameMap a.plain[i]! b.plain[i]!) &&
    a.rc.size == b.rc.size &&
    a.rc.fold (fun ok k (d, n) => ok && (b.rc.get? k).any fun (d', n') => d == d' && n == n') true

end Tables

end Near.Node.Store
