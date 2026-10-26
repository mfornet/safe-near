import Lean
import Wasm.ByteSource
import Wasm.BinaryReads

/-!
# Embedding a binary for kernel proofs

`byte_source% "file.wasm"` reads a file when the declaration using it is
elaborated and gives its bytes as a `Wasm.ByteSource`: chunks of
`chunkSize` bytes as `Nat` literals at the leaves of a complete tree, so that
the kernel reads any byte in a few steps (`Wasm/ByteSource.lean`). Paths are
relative to the package root of the file being elaborated.

`ToExpr` instances for the module syntax let elaborators state what the
decoder produces as a literal; the kernel then checks the statement by
running the decoder.

This library is kept out of `Wasm`'s import closure: the runtime does not
depend on Lean's elaborator.
-/

namespace Wasm.Embed

open Lean Elab Term Meta

deriving instance ToExpr for NumType
deriving instance ToExpr for RefType
deriving instance ToExpr for ValType
deriving instance ToExpr for FuncType
deriving instance ToExpr for Limits
deriving instance ToExpr for TableType
deriving instance ToExpr for MemType
deriving instance ToExpr for GlobalType
deriving instance ToExpr for BlockType
deriving instance ToExpr for IUnOp
deriving instance ToExpr for IBinOp
deriving instance ToExpr for IRelOp
deriving instance ToExpr for FUnOp
deriving instance ToExpr for FBinOp
deriving instance ToExpr for FRelOp
deriving instance ToExpr for CvtOp
deriving instance ToExpr for MemArg
deriving instance ToExpr for Packed
deriving instance ToExpr for Instr
deriving instance ToExpr for Func
deriving instance ToExpr for Table
deriving instance ToExpr for Mem
deriving instance ToExpr for Global
deriving instance ToExpr for SegmentMode
deriving instance ToExpr for Elem
deriving instance ToExpr for ImportDesc
deriving instance ToExpr for Import
deriving instance ToExpr for ExportDesc
deriving instance ToExpr for Export

/-- Bytes per leaf of an embedded source. -/
def chunkSize : Nat := 64

/-- A complete tree over `chunks[lo:hi]`, whose length is a power of two. -/
partial def treeExpr (chunks : Array Nat) (lo hi : Nat) : Lean.Expr :=
  if hi - lo ≤ 1 then mkApp (mkConst ``ByteTree.leaf) (mkRawNatLit (chunks[lo]?.getD 0))
  else
    let mid := (lo + hi) / 2
    mkApp2 (mkConst ``ByteTree.node) (treeExpr chunks lo mid) (treeExpr chunks mid hi)

/-- The little-endian chunks of `bytes`, padded with zero chunks to `2 ^ depth`. -/
def chunks (bytes : ByteArray) (depth : Nat) : Array Nat := Id.run do
  let mut out := #[]
  for c in [0:2 ^ depth] do
    let mut n := 0
    for j in [0:chunkSize] do
      let i := c * chunkSize + j
      if i < bytes.size then n := n + bytes[i]!.toNat <<< (8 * j)
    out := out.push n
  return out

/-- The least depth whose tree has room for `n` chunks. -/
def depthFor (n : Nat) : Nat := Id.run do
  let mut d := 0
  while 2 ^ d < n do d := d + 1
  return d

/-- The `ByteSource` literal holding `bytes`. -/
def sourceExpr (bytes : ByteArray) : Lean.Expr :=
  let depth := depthFor ((bytes.size + chunkSize - 1) / chunkSize)
  mkApp4 (mkConst ``ByteSource.mk) (treeExpr (chunks bytes depth) 0 (2 ^ depth))
    (mkRawNatLit depth) (mkRawNatLit chunkSize) (mkRawNatLit bytes.size)

/-- The bytes of a file, as a `ByteSource`, read when this term is elaborated. -/
elab "byte_source%" path:str : term => do
  return sourceExpr (← IO.FS.readBinFile path.getString)

/-- `kernel_rfl` closes an equation by `Eq.refl`, checked by the kernel
alone: the elaborator does not try to evaluate either side first. -/
elab "kernel_rfl" : tactic => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (ty, lhs, _) := tgt.eq? | throwError "kernel_rfl: the goal is not an equation"
  let pf := mkApp2 (mkConst ``Eq.refl [← getLevel ty]) ty lhs
  let name ← withOptions (Elab.async.set · false) do mkAuxLemma [] tgt pf
  goal.assign (mkConst name [])

/-! ## Code entries

`#embed_wasm_code src "file.wasm" a b` decodes the file when it is
elaborated and, for each code entry `k` in `[a, b)`, adds

* `f<i> : Wasm.Func`, the function as the decoder reads it, where `i` is its
  function index (imported functions come first);
* `code_f<i>`, the theorem that `Parser.code` at the entry's position reads
  exactly that function and stops at the next entry. The input is
  `src.input` limited to the end of the code section, as the decoder reads
  the section (`Parser.sized`);

and, for the range:

* `codes_<a>_<b>`, the list of these entries, and `reads_<a>_<b>`, that
  `Parser.code` reads them one after another (`Parser.Reads`), from the
  position of entry `a` to the end of entry `b - 1`;
* `funcTypes_<a>_<b>` (their types, from the function section) and
  `funcs_<a>_<b>` (the functions), with `zip_<a>_<b>`, that the decoder
  assembles exactly these functions from them (`entryFunc`);
* `noData_<a>_<b>`: no body uses a data index (`memory.init`,
  `data.drop`), which the decoder checks when there is no data count
  section.

The theorems about a range are checked in their own declarations, so that
the kernel's work on one range does not accumulate with the next.

Nothing here is trusted: each theorem is proved by `Eq.refl` and the kernel
checks it by running the decoder on `src`. `src` must be the byte source of
the same file.
-/

open Binary in
/-- The position of every code entry, and the end of the last one. -/
def codeEntryPositions (bytes : ByteArray) : Except String (Array Nat) := do
  let input := Input.ofBytes bytes
  let run {α} (p : Parser α) (pos : Nat) : Except String (α × Nat) :=
    match p input pos with
    | .ok r => .ok r
    | .error e => .error e.message
  let mut pos := 8
  let mut out := #[]
  while pos < bytes.size do
    let (id, p1) ← run Parser.byte pos
    let (size, p2) ← run Parser.u32 p1
    if id == 10 then
      let (n, p3) ← run Parser.u32 p2
      let mut q := p3
      for _ in [0:n] do
        out := out.push q
        let (entrySize, q') ← run Parser.u32 q
        q := q' + entrySize
      out := out.push q
      return out
    pos := p2 + size
  throw "no code section"

syntax (name := embedWasmCode) "#embed_wasm_code " ident ppSpace str ppSpace num ppSpace num : command

open Command in
@[command_elab embedWasmCode] def elabEmbedWasmCode : CommandElab := fun stx => do
  let src : Term := ⟨stx[1]⟩
  let some path := stx[2].isStrLit? | throwError "expected a path"
  let some first := stx[3].isNatLit? | throwError "expected a number"
  let some last := stx[4].isNatLit? | throwError "expected a number"
  let bytes ← IO.FS.readBinFile path
  let m ← match Binary.decode bytes with
    | .ok m => pure m
    | .error e => throwError "decoding {path}: {e.message}"
  let positions ← match codeEntryPositions bytes with
    | .ok ps => pure ps
    | .error e => throwError "reading the code entries of {path}: {e}"
  let imported := (m.imports.filter fun i => i matches { desc := .func _, .. }).size
  let ns ← getCurrNamespace
  let last := min last m.funcs.size
  let stopAll := Syntax.mkNumLit (toString positions.back!)
  for k in [first:last] do
    let idx := imported + k
    let fname := ns ++ Name.mkSimple s!"f{idx}"
    liftCoreM <| addDecl <| .defnDecl {
      name := fname, levelParams := [], type := mkConst ``Func, value := toExpr m.funcs[k]!,
      hints := .regular 0, safety := .safe }
    let fId := mkIdent fname
    let thm := ns ++ Name.mkSimple s!"code_f{idx}"
    let pos := Syntax.mkNumLit (toString positions[k]!)
    let next := Syntax.mkNumLit (toString positions[k + 1]!)
    let doc := s!"Code entry {k} (bytes {positions[k]!} to {positions[k + 1]!}) is `f{idx}`."
    liftTermElabM do
      let type ← Term.elabTerm (← `(Wasm.Binary.Parser.code { ($src).input with limit := $stopAll } $pos =
        Except.ok ((($fId).bodySize, ($fId).locals, ($fId).body), $next))) (some (mkSort 0))
      Term.synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      let some (_, lhs, _) := type.eq? | throwError "not an equation"
      addDecl <| .thmDecl { name := thm, levelParams := [], type, value := ← mkEqRefl lhs }
      addDocStringCore thm doc
  if first < last then
    let fIds := (List.range' first (last - first)).map fun k => mkIdent (ns ++ Name.mkSimple s!"f{imported + k}")
    let entries ← fIds.toArray.mapM fun f => `((($f).bodySize, ($f).locals, ($f).body))
    let mut proof ← `(rfl)
    for k in (List.range' first (last - first)).reverse do
      let next := Syntax.mkNumLit (toString positions[k + 1]!)
      let code := mkIdent (ns ++ Name.mkSimple s!"code_f{imported + k}")
      proof ← `(⟨$next, $code, $proof⟩)
    let name := mkIdent (Name.mkSimple s!"reads_{first}_{last}")
    let list := mkIdent (Name.mkSimple s!"codes_{first}_{last}")
    let pos := Syntax.mkNumLit (toString positions[first]!)
    let stop := Syntax.mkNumLit (toString positions[last]!)
    let docOf (text : String) : TSyntax ``Lean.Parser.Command.docComment :=
      ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (text ++ " -/")]⟩
    elabCommand (← `($(docOf s!"Code entries {first} to {last - 1}."):docComment
      noncomputable def $list : List (Nat × List Wasm.ValType × Wasm.Expr) := [$entries,*]))
    elabCommand (← `($(docOf s!"Code entries {first} to {last - 1} decode one after another."):docComment
      theorem $name : Wasm.Binary.Parser.Reads Wasm.Binary.Parser.code
        { ($src).input with limit := $stopAll } $list $pos $stop := $proof))
    let range := s!"{first}_{last}"
    let types := mkIdent (Name.mkSimple s!"funcTypes_{range}")
    let fs := mkIdent (Name.mkSimple s!"funcs_{range}")
    let typeLits := ((List.range' first (last - first)).map fun k =>
      Syntax.mkNumLit (toString m.funcs[k]!.type)).toArray
    elabCommand (← `($(docOf s!"The types of functions {imported + first} to {imported + last - 1}."):docComment
      def $types : List Nat := [$typeLits,*]))
    elabCommand (← `($(docOf s!"Functions {imported + first} to {imported + last - 1}."):docComment
      noncomputable def $fs : List Wasm.Func := [$(fIds.toArray),*]))
    elabCommand (← `($(docOf s!"The decoder assembles functions {imported + first} to {imported + last - 1} from their types and entries."):docComment
      theorem $(mkIdent (Name.mkSimple s!"zip_{range}")) :
        List.zipWith Wasm.Binary.Parser.entryFunc $types $list = $fs := by kernel_rfl))
    elabCommand (← `($(docOf s!"No body among code entries {first} to {last - 1} uses a data index."):docComment
      theorem $(mkIdent (Name.mkSimple s!"noData_{range}")) :
        (List.any $list fun e => Wasm.Binary.Parser.anyUsesDataIndex e.2.2) = false := by kernel_rfl))

/-! ## The other sections

`#embed_wasm_sections "file.wasm"` adds, in the current namespace, the
decoded contents of every section but code and data, as literals: `types`,
`imports`, `funcTypes` (the function section), `tables`, `mems`, `globals`,
`exports`, `elems`. Statements about decoding the file mention them; their
proofs are the kernel's.
-/

syntax (name := embedWasmSections) "#embed_wasm_sections " str : command

open Command in
@[command_elab embedWasmSections] def elabEmbedWasmSections : CommandElab := fun stx => do
  let some path := stx[1].isStrLit? | throwError "expected a path"
  let m ← match Binary.decode (← IO.FS.readBinFile path) with
    | .ok m => pure m
    | .error e => throwError "decoding {path}: {e.message}"
  let ns ← getCurrNamespace
  let add (name : String) (type : Lean.Expr) (value : Lean.Expr) (doc : String) : CommandElabM Unit := do
    let n := ns ++ Name.mkSimple name
    liftCoreM <| addDecl <| .defnDecl {
      name := n, levelParams := [], type, value, hints := .regular 0, safety := .safe }
    liftTermElabM <| addDocStringCore n doc
  add "types" (toTypeExpr (Array FuncType)) (toExpr m.types) "The type section, as decoded."
  add "imports" (toTypeExpr (Array Import)) (toExpr m.imports) "The import section, as decoded."
  add "funcTypes" (toTypeExpr (Array Nat)) (toExpr (m.funcs.map (·.type)))
    "The function section (the type of each defined function), as decoded."
  add "tables" (toTypeExpr (Array Table)) (toExpr m.tables) "The table section, as decoded."
  add "mems" (toTypeExpr (Array Mem)) (toExpr m.mems) "The memory section, as decoded."
  add "globals" (toTypeExpr (Array Global)) (toExpr m.globals) "The global section, as decoded."
  add "exports" (toTypeExpr (Array Export)) (toExpr m.exports) "The export section, as decoded."
  add "elems" (toTypeExpr (Array Elem)) (toExpr m.elems) "The element section, as decoded."

end Wasm.Embed
