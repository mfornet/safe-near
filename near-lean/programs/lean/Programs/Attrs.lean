import Lean

/-!
# `@[spec_of]` and `@[proves]` — attributes linking specs, code, and proofs

Copied from Talos `codelib/CodeLib/Attrs.lean`. The runtime behaviour is
intentionally minimal: the attributes only need to exist so the source
typechecks. Their meaning is for tooling that reads specs off the source and
reports which ones are proven.

## `@[spec_of <kind> "qualified::name"]`

Marks a `def Name : Prop := …` as a formal spec linked to code or to a
crate-level property. `<kind>` is one of:

* `rust-exported` — `target` is `crate::fn_name`, naming a wasm-exported
  Rust function (`#[unsafe(no_mangle)] pub extern "C" fn`).
* `rust-exported-partial` — the same target provenance, when the public
  proposition constrains every finite return but does not prove termination.
* `rust-internal` — any other Rust path (`crate::module::fn`).
* `rust-internal-partial` — the same internal target provenance for a
  partial-correctness proposition.
* `crate-property` — `target` is `crate::property_name`, naming a property of
  the crate rather than pretending that a composing function exists.
* `lean` — any Lean symbol.

## `@[proves SpecName]`

Marks a `theorem` as a verification of the named formal spec. `SpecName`
is the fully qualified name of a `@[spec_of …] def`.
-/

open Lean

namespace Programs

/-- `@[spec_of "<kind>" "qualified::name"]` — tag a `def : Prop` as a
formal spec linked to code or to a crate-level property. See module docstring. -/
syntax (name := spec_of) "spec_of" str str : attr

/-- `@[proves SpecName]` — tag a theorem as a verification of the named
formal spec. See module docstring. -/
syntax (name := proves) "proves" ident : attr

initialize
  Lean.registerBuiltinAttribute {
    name            := `spec_of
    descr           := "Mark a `def : Prop` as a formal spec linked to a code symbol."
    applicationTime := .afterCompilation
    add             := fun _ _ _ => pure ()
    erase           := fun _ => pure ()
  }

initialize
  Lean.registerBuiltinAttribute {
    name            := `proves
    descr           := "Mark a theorem as a verification of a named formal spec."
    applicationTime := .afterCompilation
    add             := fun _ _ _ => pure ()
    erase           := fun _ => pure ()
  }

end Programs
