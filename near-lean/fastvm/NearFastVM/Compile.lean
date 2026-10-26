import NearFastVM.Ins

/-!
# Compiling a function body

The body of a validated function becomes a flat array of `Ins`. The compiler follows the operand stack height
of the body statically, so a branch knows how many values to carry and where to put them, and an operand is
addressed by its slot. Every Wasm instruction becomes one instruction of the stream with the gas the
specification charges before it (`NearVM.Run.nextInstructionGas`): `block` has none, `loop` and `if` are
charged on entry, and the jump that skips an `else` branch and the return at the end of a body are free.
A branch to a `loop` label also pays for the loop (`loopBackedge`).

Code after a branch, `return` or `unreachable` in the same sequence is never executed and is not compiled.
Anything the engine does not run makes `compile` fail (`none`), and the caller runs the specification instead:
reference types, tables other than `call_indirect`, `memory.init` and `data.drop`.
-/

namespace NearFastVM

open Wasm Wasm.Near

structure BrLabel where
  isLoop : Bool
  /-- Operand stack height below the block's parameters. -/
  height : Nat
  /-- Values a branch to the label carries. -/
  arity : Nat
  /-- First instruction of a loop's body. -/
  target : Nat
  codePatches : Array Nat := #[]
  tablePatches : Array (Nat × Nat) := #[]
  deriving Inhabited

structure CS where
  /-- The slot of operand height zero: the number of locals. -/
  base : Nat
  /-- Results of the function. -/
  nres : Nat
  reg : UInt64
  code : Array Ins := #[]
  tables : Array (Array Ins) := #[]
  colds : Array Instr := #[]
  h : Nat := 0
  maxH : Nat := 0
  labels : Array BrLabel := #[]
  ok : Bool := true

namespace CS

@[inline]
def slot (cs : CS) (k : Nat) : UInt32 :=
  (2 * (cs.base + k)).toUInt32

def emit (cs : CS) (i : Ins) : CS :=
  { cs with code := cs.code.push i }

def setH (cs : CS) (h : Nat) : CS :=
  { cs with
    h := h, maxH := max cs.maxH h }

def fail (cs : CS) : CS :=
  { cs with ok := false }

/-- Give the forward branches to `lab` the target `pc`. -/
def patch (cs : CS) (lab : BrLabel) (pc : Nat) : CS :=
  let code :=
    lab.codePatches.foldl (fun code i => code.modify i fun ins => { ins with y := pc.toUInt32 })
      cs.code
  let tables :=
    lab.tablePatches.foldl
      (fun ts (t, e) =>
        ts.modify t fun entries => entries.modify e fun ins => { ins with y := pc.toUInt32 })
      cs.tables
  { cs with
    code, tables }

end CS

/-- The instruction that branches to the `l`-th label with the operand stack at height `cs.h`, and the label
whose end it jumps to, if it is a forward branch. `cost` is the instruction's charge. -/
def branchIns (cs : CS) (l : Nat) (cost : UInt64) : Ins × Option Nat :=
  if l < cs.labels.size then
    let li := cs.labels.size - 1 - l
    let lab := cs.labels[li]!
    let src := cs.base + cs.h - lab.arity
    let dst := cs.base + lab.height
    let z := if lab.arity == 0 || src == dst then 0 else lab.arity
    ({ op := .br, cost := cost, x := (2 * src).toUInt32, w := (2 * dst).toUInt32, z := z.toUInt32,
       y := if lab.isLoop then lab.target.toUInt32 else 0,
       cost2 := if lab.isLoop then cs.reg else 0 },
      if lab.isLoop then none else some li)
  else
    ({ op := .ret, cost := cost, x := (2 * (cs.base + cs.h - cs.nres)).toUInt32,
       z := cs.nres.toUInt32 },
      none)

def addPatch (cs : CS) (li : Option Nat) (codeIdx : Nat) : CS :=
  match li with
  | none => cs
  | some li =>
    { cs with
      labels :=
        cs.labels.modify li fun lab => { lab with codePatches := lab.codePatches.push codeIdx } }

def loadOp (t : NumType) (packed : Option Packed) : Option Op :=
  match t, packed with
  | .i32, none | .f32, none => some .ld32
  | .i64, none | .f64, none => some .ld64
  | .i32, some p | .i64, some p =>
    match p.bits, p.signed, t with
    | 8, false, _ => some .ld8u
    | 8, true, .i32 => some .ld8s32
    | 8, true, _ => some .ld8s64
    | 16, false, _ => some .ld16u
    | 16, true, .i32 => some .ld16s32
    | 16, true, _ => some .ld16s64
    | 32, false, .i64 => some .ld32
    | 32, true, .i64 => some .ld32s64
    | _, _, _ => none
  | _, _ => none

def storeOp (t : NumType) (bits : Option Nat) : Option Op :=
  match t, bits with
  | .i32, none | .f32, none => some .st32
  | .i64, none | .f64, none => some .st64
  | _, some 8 => some .st8
  | _, some 16 => some .st16
  | _, some 32 => some .st32
  | _, _ => none

/-- Operands popped by a floating-point or conversion instruction (the `cold` operations). -/
def coldPops : Instr → Option Nat
  | .f32_unop _ | .f64_unop _ | .cvt _ => some 1
  | .f32_binop _ | .f64_binop _ | .f32_relop _ | .f64_relop _ => some 2
  | _ => none

def blockSig (inst : ModuleInst) : BlockType → FuncType
  | .empty => { params := [], results := [] }
  | .val t => { params := [], results := [t] }
  | .index i => inst.types[i]?.getD { params := [], results := [] }

mutual
partial def goList (cx : Ctx) (cs : CS) : List Instr → CS
  | [] => cs
  | i :: rest =>
    let (cs, continues) := goInstr cx cs i
    if continues && cs.ok then goList cx cs rest else cs
/-- Compile one instruction; `false` when control never reaches the next one. -/
partial def goInstr (cx : Ctx) (cs : CS) (i : Instr) : CS × Bool :=
  let reg := cs.reg
  let h := cs.h
  let one (op : Op) : CS × Bool := (cs.emit { op, cost := reg }, true)
  match i with
  | .unreachable => (cs.emit { op := .unreachable, cost := reg }, false)
  | .nop => one .nop
  | .block bt body =>
    let ft := blockSig cx.inst bt
    let np := ft.params.length
    let lab : BrLabel :=
      { isLoop := false, height := h - np, arity := ft.results.length, target := 0 }
    let cs := { cs with labels := cs.labels.push lab }
    let cs := goList cx cs body
    let lab := cs.labels.back!
    let cs := { cs with labels := cs.labels.pop }
    let cs := cs.patch lab cs.code.size
    (cs.setH (h - np + ft.results.length), true)
  | .loop bt body =>
    let ft := blockSig cx.inst bt
    let np := ft.params.length
    let cs := cs.emit { op := .nop, cost := reg }
    let lab : BrLabel := { isLoop := true, height := h - np, arity := np, target := cs.code.size }
    let cs := { cs with labels := cs.labels.push lab }
    let cs := goList cx cs body
    let cs := { cs with labels := cs.labels.pop }
    (cs.setH (h - np + ft.results.length), true)
  | .«if» bt thenBody elseBody =>
    let ft := blockSig cx.inst bt
    let np := ft.params.length
    let h1 := h - 1
    let lh := h1 - np
    let ifIdx := cs.code.size
    let cs := cs.emit { op := .if_z, cost := reg, x := (cs.slot h1) }
    let lab : BrLabel := { isLoop := false, height := lh, arity := ft.results.length, target := 0 }
    let cs := { cs with labels := cs.labels.push lab }
    let cs := cs.setH h1
    let cs := goList cx cs thenBody
    let cs :=
      if elseBody.isEmpty then
        -- the empty else branch: the stack keeps its parameters, which are the results
        let cs :=
          { cs with
            code := cs.code.modify ifIdx fun ins => { ins with y := cs.code.size.toUInt32 } }
        cs
      else
        let jmpIdx := cs.code.size
        let cs := cs.emit { op := .jmp }
        let cs :=
          { cs with
            labels :=
              cs.labels.modify (cs.labels.size - 1) fun lab =>
                { lab with codePatches := lab.codePatches.push jmpIdx } }
        let cs :=
          { cs with
            code := cs.code.modify ifIdx fun ins => { ins with y := cs.code.size.toUInt32 } }
        let cs := cs.setH h1
        goList cx cs elseBody
    let lab := cs.labels.back!
    let cs := { cs with labels := cs.labels.pop }
    let cs := cs.patch lab cs.code.size
    (cs.setH (lh + ft.results.length), true)
  | .br l =>
    let reg2 := reg
    let (ins, li) := branchIns cs l reg2
    -- an unconditional branch to a loop pays for the back edge in its own charge
    let ins :=
      if ins.op == .br then
        { ins with
          cost := ins.cost + ins.cost2, cost2 := 0 }
      else ins
    let idx := cs.code.size
    (addPatch (cs.emit ins) li idx, false)
  | .br_if l =>
    let h1 := h - 1
    let cs1 := { cs with h := h1 }
    let (ins, li) := branchIns cs1 l reg
    if ins.op == .ret then
      -- skip the return when the condition is zero
      let ifIdx := cs.code.size
      let cs := cs.emit { op := .if_z, cost := reg, x := cs.slot h1 }
      let cs := cs.emit { ins with cost := 0 }
      let cs :=
        { cs with code := cs.code.modify ifIdx fun i => { i with y := cs.code.size.toUInt32 } }
      (cs.setH h1, true)
    else
      let idx := cs.code.size
      let ins :=
        { ins with
          op := .br_if, imm := (cs.slot h1).toUInt64 }
      (addPatch (cs.emit ins) li idx |>.setH h1, true)
  | .br_table ls d =>
    let h1 := h - 1
    let cs1 := { cs with h := h1 }
    let tIdx := cs.tables.size
    let retPc := cs.code.size + 1
    let targets := (ls ++ [d]).toArray
    let (entries, labels) :=
      Id.run do
        let mut entries : Array Ins := #[]
        let mut labels := cs.labels
        for l in targets do
          let (ins, li) := branchIns { cs1 with labels := labels } l reg
          if ins.op == .ret then
            -- a branch out of the function: every such entry goes to the return right after the table jump
            entries := entries.push { op := .br, y := retPc.toUInt32 }
          else
            if let some li := li then
              labels :=
                labels.modify li fun lab =>
                  { lab with tablePatches := lab.tablePatches.push (tIdx, entries.size) }
            entries := entries.push { ins with cost := 0 }
        return (entries, labels)
    let cs :=
      { cs with
        tables := cs.tables.push entries, labels := labels }
    let cs := cs.emit { op := .br_table, cost := reg, x := cs.slot h1, imm := tIdx.toUInt64 }
    let cs := cs.emit { op := .ret, x := cs.slot (h1 - cs.nres), z := cs.nres.toUInt32 }
    (cs, false)
  | .«return» =>
    (cs.emit { op := .ret, cost := reg, x := cs.slot (h - cs.nres), z := cs.nres.toUInt32 }, false)
  | .call f =>
    match cx.inst.funcAddrs[f]? with
    | none => (cs.fail, false)
    | some addr =>
      match cx.funcs[addr]? with
      | none => (cs.fail, false)
      | some fn =>
        let ft := fn.type
        let np := ft.params.length
        let cs := cs.emit { op := .call, cost := reg, x := cs.slot (h - np), imm := addr.toUInt64 }
        (cs.setH (h - np + ft.results.length), true)
  | .call_indirect ty t =>
    match cx.inst.types[ty]?, cx.inst.tableAddrs[t]? with
    | some ft, some _ =>
      let np := ft.params.length
      let ins : Ins :=
        { op := .call_indirect, cost := reg, x := cs.slot (h - 1), y := ty.toUInt32,
          z := np.toUInt32, w := t.toUInt32 }
      let cs := cs.emit ins
      (cs.setH (h - 1 - np + ft.results.length), true)
    | _, _ => (cs.fail, false)
  | .drop => (cs.emit { op := .nop, cost := reg } |>.setH (h - 1), true)
  | .select _ =>
    (cs.emit { op := .select, cost := reg, x := cs.slot (h - 3) } |>.setH (h - 2), true)
  | .local_get i =>
    (cs.emit { op := .local_get, cost := reg, x := cs.slot h, y := (2 * i).toUInt32 } |>.setH
        (h + 1),
      true)
  | .local_set i =>
    (cs.emit { op := .local_set, cost := reg, x := cs.slot (h - 1), y := (2 * i).toUInt32 } |>.setH
        (h - 1),
      true)
  | .local_tee i =>
    (cs.emit { op := .local_tee, cost := reg, x := cs.slot (h - 1), y := (2 * i).toUInt32 }, true)
  | .global_get g =>
    if g < cx.inst.globalAddrs.size then
      (cs.emit { op := .global_get, cost := reg, x := cs.slot h, y := (2 * g).toUInt32 } |>.setH
          (h + 1),
        true)
    else (cs.fail, false)
  | .global_set g =>
    if g < cx.inst.globalAddrs.size then
      (cs.emit
            { op := .global_set, cost := reg, x := cs.slot (h - 1), y := (2 * g).toUInt32 } |>.setH
          (h - 1),
        true)
    else (cs.fail, false)
  | .load t packed arg =>
    match cx.hasMem, loadOp t packed with
    | true, some op =>
      (cs.emit { op, cost := reg, x := cs.slot (h - 1), imm := arg.offset.toUInt64 }, true)
    | _, _ => (cs.fail, false)
  | .store t bits arg =>
    match cx.hasMem, storeOp t bits with
    | true, some op =>
      (cs.emit { op, cost := reg, x := cs.slot (h - 2), imm := arg.offset.toUInt64 } |>.setH
          (h - 2),
        true)
    | _, _ => (cs.fail, false)
  | .memory_size =>
    if cx.hasMem then
      (cs.emit { op := .memory_size, cost := reg, x := cs.slot h } |>.setH (h + 1), true)
    else (cs.fail, false)
  | .memory_grow =>
    if cx.hasMem then (cs.emit { op := .memory_grow, x := cs.slot (h - 1) }, true)
    else (cs.fail, false)
  | .memory_fill =>
    if cx.hasMem then (cs.emit { op := .memory_fill, x := cs.slot (h - 3) } |>.setH (h - 3), true)
    else (cs.fail, false)
  | .memory_copy =>
    if cx.hasMem then (cs.emit { op := .memory_copy, x := cs.slot (h - 3) } |>.setH (h - 3), true)
    else (cs.fail, false)
  | .i32_const n =>
    (cs.emit { op := .const, cost := reg, x := cs.slot h, imm := n.toUInt64 } |>.setH (h + 1), true)
  | .i64_const n =>
    (cs.emit { op := .const, cost := reg, x := cs.slot h, imm := n } |>.setH (h + 1), true)
  | .f32_const b =>
    (cs.emit { op := .const, cost := reg, x := cs.slot h, imm := b.toUInt64 } |>.setH (h + 1), true)
  | .f64_const b =>
    (cs.emit { op := .const, cost := reg, x := cs.slot h, imm := b } |>.setH (h + 1), true)
  | .i32_eqz => (cs.emit { op := .i32_eqz, cost := reg, x := cs.slot (h - 1) }, true)
  | .i64_eqz => (cs.emit { op := .i64_eqz, cost := reg, x := cs.slot (h - 1) }, true)
  | _ =>
    match Op.ofNumeric? i with
    | some op =>
      let pops : Nat :=
        match i with
        | .i32_binop _ | .i64_binop _ | .i32_relop _ | .i64_relop _ => 2
        | _ => 1
      let cs := cs.emit { op, cost := reg, x := cs.slot (h - pops) }
      (cs.setH (h - pops + 1), true)
    | none =>
      match coldPops i with
      | some pops =>
        let cs := { cs with colds := cs.colds.push i }
        let ins : Ins :=
          { op := .cold, cost := reg, x := cs.slot (h - pops), z := pops.toUInt32,
            imm := (cs.colds.size - 1).toUInt64 }
        let cs := cs.emit ins
        (cs.setH (h - pops + 1), true)
      | none => (cs.fail, false)
end

def valSize : ValType → Nat
  | .num .i32 | .num .f32 => 4
  | _ => 8

def isRef : ValType → Bool
  | .ref _ => true
  | _ => false

/-- The frame activation charge: `NearVM.Run.activationGas` of the locals the call creates. -/
def activationOf (regular : Nat) (locals : List ValType) : Nat :=
  ((64 + (locals.map valSize).sum + 7) / 8) * regular

/-- Compile a function of the module instance, or `none` if the engine does not run it. -/
def compileFunc (cx : Ctx) (ft : FuncType) (f : Func) : Option FnCode :=
  let all := ft.params ++ f.locals
  if all.any isRef || ft.results.any isRef then none
  else
    if cx.regular ≥ 2 ^ 40 then none
    else
      let nlocals := all.length
      let cs : CS := { base := nlocals, nres := ft.results.length, reg := cx.regular.toUInt64 }
      let cs := goList cx cs f.body
      -- falling off the end of the body returns
      let cs :=
        cs.emit
          { op := .ret, x := (2 * (nlocals + cs.h - ft.results.length)).toUInt32,
            z := ft.results.length.toUInt32 }
      if cs.ok && nlocals + cs.maxH + 8 < 2 ^ 31 && activationOf cx.regular all < 2 ^ 40 then
        some
          { code := cs.code, tables := cs.tables, colds := cs.colds, nlocals,
            nparams := ft.params.length, frameSlots := 2 * (nlocals + cs.maxH + 1),
            results := ft.results, activation := activationOf cx.regular all }
      else none

end NearFastVM
