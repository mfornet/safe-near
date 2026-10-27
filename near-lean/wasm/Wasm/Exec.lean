import Wasm.Store
import Wasm.Numeric

/-!
# Execution

Section 4.4 of the specification as one deterministic, executable
small-step machine. A `Config` is a store and a thread; `step` performs one
instruction (or one administrative action: ending a block, returning from a
call) and the proof-side relation `Step` is defined from it.

The thread keeps one operand stack for all frames. A label records the
stack height at its entry, its branch arity, the code that follows the
block, and, for a loop, the body to re-enter on a branch. A call frame
records its locals, its module instance, its result arity, the stack height
at entry, its labels and the code it is executing.
-/

namespace Wasm

structure Label where
  arity : Nat
  height : Nat
  /-- The code after the block. -/
  rest : List Instr
  /-- For a loop, its body: a branch to the label re-enters it. -/
  loop : Option (List Instr)

structure CallFrame where
  locals : Array Value
  inst : Nat
  arity : Nat
  height : Nat
  labels : List Label
  code : List Instr

structure Thread where
  stack : Array Value
  frames : List CallFrame

/-- Implementation limits that make runaway programs trap. -/
structure ExecLimits where
  maxCallDepth : Nat := 10000
deriving Repr, Inhabited

structure Config (H : Type) where
  store : Store H
  thread : Thread
  limits : ExecLimits

inductive StepResult (H : Type) where
  | next (cfg : Config H)
  | done (values : List Value) (store : Store H)
  | trap (reason : Trap) (store : Store H)

namespace Exec

/-- The exact instruction the machine will execute next, if it is at one. -/
def _root_.Wasm.Config.nextInstr? (c : Config H) : Option Instr :=
  c.thread.frames.head?.bind (·.code.head?)

def _root_.Wasm.Config.callDepth (c : Config H) : Nat := c.thread.frames.length

/-- The value on top of the operand stack. -/
def _root_.Wasm.Config.stackTop? (c : Config H) : Option Value := c.thread.stack.back?

/-- Whether the `l`-th enclosing label of the current frame is a loop. -/
def _root_.Wasm.Config.labelIsLoop (c : Config H) (l : Nat) : Bool :=
  match c.thread.frames.head? with
  | some frame => (frame.labels[l]?.map (·.loop.isSome)).getD false
  | none => false

/-- The locals of the current frame. -/
def _root_.Wasm.Config.locals (c : Config H) : Array Value :=
  (c.thread.frames.head?.map (·.locals)).getD #[]

/-- The host state of a step result. -/
def _root_.Wasm.StepResult.host : StepResult H → H
  | .next c => c.store.host
  | .done _ s => s.host
  | .trap _ s => s.host

def _root_.Wasm.StepResult.store : StepResult H → Store H
  | .next c => c.store
  | .done _ s => s
  | .trap _ s => s

/-! ## Stack helpers -/

def popN (stack : Array Value) (n : Nat) : Array Value × List Value :=
  (stack.shrink (stack.size - n), (stack.extract (stack.size - n) stack.size).toList)

/-- What executing one instruction asks the frame to do next. -/
inductive EffectKind where
  /-- Continue with the given stack, labels and code in the current frame. -/
  | continue (stack : Array Value) (labels : List Label) (code : List Instr) (locals : Array Value)
  /-- Call the function at a store address with arguments already popped. -/
  | call (stack : Array Value) (addr : Nat) (rest : List Instr)
  /-- Return from the current frame. -/
  | «return» (stack : Array Value)
  | trap (reason : Trap)

/-- The result of executing one instruction: the store after it and what to
do next. A structure, so that `store` is a projection proofs can see through. -/
structure Effect (H : Type) where
  store : Store H
  kind : EffectKind

namespace Effect
@[inline] def «continue» (store : Store H) (stack : Array Value) (labels : List Label)
    (code : List Instr) (locals : Array Value) : Effect H :=
  ⟨store, .continue stack labels code locals⟩
@[inline] def call (store : Store H) (stack : Array Value) (addr : Nat) (rest : List Instr) :
    Effect H := ⟨store, .call stack addr rest⟩
@[inline] def «return» (store : Store H) (stack : Array Value) : Effect H :=
  ⟨store, .return stack⟩
@[inline] def trap (store : Store H) (reason : Trap) : Effect H := ⟨store, .trap reason⟩
@[simp] theorem continue_store (s : Store H) (a b c d) :
    (Effect.continue s a b c d).store = s := rfl
@[simp] theorem call_store (s : Store H) (a b c) : (Effect.call s a b c).store = s := rfl
@[simp] theorem return_store (s : Store H) (a) : (Effect.return s a).store = s := rfl
@[simp] theorem trap_store (s : Store H) (a) : (Effect.trap s a).store = s := rfl
end Effect

/-- Branch to the `l`-th enclosing label. The function body is the outermost
label, so a branch past every block label returns. -/
def branch (store : Store H) (stack : Array Value) (labels : List Label) (locals : Array Value)
    (l : Nat) : Effect H :=
  match labels[l]? with
  | none => .return store stack
  | some label =>
    let (stack, values) := popN stack label.arity
    let stack := stack.shrink label.height ++ values.toArray
    match label.loop with
    | some body => .continue store stack (labels.drop l) body locals
    | none => .continue store stack (labels.drop (l + 1)) label.rest locals

def blockType (inst : ModuleInst) : BlockType → FuncType
  | .empty => { params := [], results := [] }
  | .val t => { params := [], results := [t] }
  | .index i => inst.types[i]!

/-- Read `len` bytes at `addr + offset` from the frame's memory. -/
def loadNat (store : Store H) (inst : ModuleInst) (arg : MemArg) (addr : UInt32) (len : Nat) :
    Option Nat := do
  let mem ← store.memOf inst
  mem.readNat (addr.toNat + arg.offset) len

def storeNat (store : Store H) (inst : ModuleInst) (arg : MemArg) (addr : UInt32) (len : Nat)
    (v : Nat) : Option (Store H) := do
  let mem ← store.memOf inst
  let mem ← mem.writeNat (addr.toNat + arg.offset) len v
  return store.setMemOf inst mem

/-- A memory store as an instruction effect: `k` continues with the written
store; out of bounds traps with the store unchanged. -/
def storeEffect (store : Store H) (inst : ModuleInst) (arg : MemArg) (addr : UInt32) (len : Nat)
    (v : Nat) (k : Store H → Effect H) : Effect H :=
  match storeNat store inst arg addr len v with
  | none => .trap store .outOfBoundsMemoryAccess
  | some store => k store

/-- `storeEffect` as it runs. `storeEffect` keeps the store for the trap
while it writes, so every store instruction copied a whole memory page. This
decides first and then writes the memory in place: `Array.modify` hands it
over unshared. -/
def storeEffectInPlace (store : Store H) (inst : ModuleInst) (arg : MemArg) (addr : UInt32)
    (len : Nat) (v : Nat) (k : Store H → Effect H) : Effect H :=
  match inst.memAddrs[0]? with
  | none => .trap store .outOfBoundsMemoryAccess
  | some a =>
    match store.mems[a]? with
    | none => .trap store .outOfBoundsMemoryAccess
    | some mem =>
      let at_ := addr.toNat + arg.offset
      if mem.inBounds at_ len then
        k { store with mems := store.mems.modify a fun mem =>
          (List.range len).foldl (fun m i => m.write8 (at_ + i) (UInt8.ofNat (v >>> (8 * i)))) mem }
      else .trap store .outOfBoundsMemoryAccess

@[csimp] theorem storeEffect_eq_inPlace : @storeEffect = @storeEffectInPlace := by
  funext H store inst arg addr len v k
  unfold storeEffect storeEffectInPlace storeNat Store.memOf Store.setMemOf Memory.writeNat
  cases ha : inst.memAddrs[0]? with
  | none => simp
  | some a =>
    cases hm : store.mems[a]? with
    | none => simp [hm]
    | some mem =>
      have hlt : a < store.mems.size := (Array.getElem?_eq_some_iff.mp hm).1
      have hget : store.mems[a] = mem := (Array.getElem?_eq_some_iff.mp hm).2
      by_cases hb : mem.inBounds (addr.toNat + arg.offset) len
      · simp [hm, hb]
        congr 2
        apply Array.ext
        · simp
        · intro i h₁ h₂
          rw [Array.getElem_setIfInBounds (by simpa using h₁), Array.getElem_modify]
          split <;> simp_all
      · simp [hm, hb]

def tableOf (store : Store H) (inst : ModuleInst) (t : Nat) : Option (Nat × TableInst) := do
  let addr ← inst.tableAddrs[t]?
  let table ← store.tables[addr]?
  return (addr, table)

def setTable (store : Store H) (addr : Nat) (table : TableInst) : Store H :=
  { store with tables := store.tables.set! addr table }

def evalMemOp (store : Store H) (inst : ModuleInst) (stack : Array Value) (labels : List Label)
    (rest : List Instr) (locals : Array Value) (k : Memory → Option Memory) : Effect H :=
  match store.memOf inst with
  | none => .trap store (.host "no memory")
  | some mem =>
    match k mem with
    | some mem => .continue (store.setMemOf inst mem) stack labels rest locals
    | none => .trap store .outOfBoundsMemoryAccess

def i32 (v : Value) : UInt32 := match v with | .i32 n => n | _ => 0

/-- Execute one instruction. `stack` already holds the operands. -/
def instr (store : Store H) (inst : ModuleInst) (locals : Array Value) (stack : Array Value)
    (labels : List Label) (i : Instr) (rest : List Instr) : Effect H :=
  let cont (store : Store H) (stack : Array Value) := Effect.continue store stack labels rest locals
  let pop1 (stack : Array Value) : Array Value × Value :=
    (stack.pop, stack.back?.getD default)
  let pop2 (stack : Array Value) : Array Value × Value × Value :=
    let (s, b) := pop1 stack
    let (s, a) := pop1 s
    (s, a, b)
  let pop3 (stack : Array Value) : Array Value × Value × Value × Value :=
    let (s, c) := pop1 stack
    let (s, b) := pop1 s
    let (s, a) := pop1 s
    (s, a, b, c)
  let withMem := evalMemOp store inst
  match i with
  | .unreachable => .trap store .unreachable
  | .nop => cont store stack
  | .block bt body =>
    let ft := blockType inst bt
    let label : Label :=
      { arity := ft.results.length, height := stack.size - ft.params.length,
        rest := rest, loop := none }
    .continue store stack (label :: labels) body locals
  | .loop bt body =>
    let ft := blockType inst bt
    let label : Label :=
      { arity := ft.params.length, height := stack.size - ft.params.length,
        rest := rest, loop := some body }
    .continue store stack (label :: labels) body locals
  | .«if» bt thenBody elseBody =>
    let (stack, c) := pop1 stack
    let ft := blockType inst bt
    let label : Label :=
      { arity := ft.results.length, height := stack.size - ft.params.length,
        rest := rest, loop := none }
    .continue store stack (label :: labels) (if i32 c != 0 then thenBody else elseBody) locals
  | .br l => branch store stack labels locals l
  | .br_if l =>
    let (stack, c) := pop1 stack
    if i32 c != 0 then branch store stack labels locals l else cont store stack
  | .br_table ls d =>
    let (stack, c) := pop1 stack
    branch store stack labels locals (ls[(i32 c).toNat]?.getD d)
  | .return => .return store stack
  | .call f =>
    match inst.funcAddrs[f]? with
    | some addr => .call store stack addr rest
    | none => .trap store (.host "unknown function")
  | .call_indirect ty t =>
    let (stack, idx) := pop1 stack
    match tableOf store inst t with
    | none => .trap store (.host "unknown table")
    | some (_, table) =>
      match table.elems[(i32 idx).toNat]? with
      | none => .trap store .undefinedElement
      | some (.null _) => .trap store .uninitializedElement
      | some (.extern _) => .trap store .indirectCallTypeMismatch
      | some (.func addr) =>
        match store.funcs[addr]? with
        | none => .trap store (.host "dangling function reference")
        | some fn =>
          if fn.type == inst.types[ty]! then .call store stack addr rest
          else .trap store .indirectCallTypeMismatch
  | .ref_null t => cont store (stack.push (.ref (.null t)))
  | .ref_is_null =>
    let (stack, r) := pop1 stack
    let isNull := match r with | .ref (.null _) => true | _ => false
    cont store (stack.push (.i32 (Numeric.bool isNull)))
  | .ref_func f => cont store (stack.push (.ref (.func inst.funcAddrs[f]!)))
  | .drop => cont store stack.pop
  | .select _ =>
    let (stack, a, b, c) := pop3 stack
    cont store (stack.push (if i32 c != 0 then a else b))
  | .local_get i => cont store (stack.push locals[i]!)
  | .local_set i =>
    let (stack, v) := pop1 stack
    .continue store stack labels rest (locals.set! i v)
  | .local_tee i =>
    let v := stack.back?.getD default
    .continue store stack labels rest (locals.set! i v)
  | .global_get g => cont store (stack.push store.globals[inst.globalAddrs[g]!]!.value)
  | .global_set g =>
    let (stack, v) := pop1 stack
    let addr := inst.globalAddrs[g]!
    let store := { store with globals := store.globals.modify addr ({ · with value := v }) }
    cont store stack
  | .table_get t =>
    let (stack, idx) := pop1 stack
    match tableOf store inst t with
    | none => .trap store (.host "unknown table")
    | some (_, table) =>
      match table.elems[(i32 idx).toNat]? with
      | some r => cont store (stack.push (.ref r))
      | none => .trap store .outOfBoundsTableAccess
  | .table_set t =>
    let (stack, idx, v) := pop2 stack
    match tableOf store inst t, v with
    | some (addr, table), .ref r =>
      if (i32 idx).toNat < table.elems.size then
        cont (setTable store addr { table with elems := table.elems.set! (i32 idx).toNat r }) stack
      else .trap store .outOfBoundsTableAccess
    | _, _ => .trap store (.host "table.set: bad operands")
  | .table_size t =>
    match tableOf store inst t with
    | some (_, table) => cont store (stack.push (.i32 (UInt32.ofNat table.elems.size)))
    | none => .trap store (.host "unknown table")
  | .table_grow t =>
    let (stack, v, n) := pop2 stack
    match tableOf store inst t, v with
    | some (addr, table), .ref r =>
      let newSize := table.elems.size + (i32 n).toNat
      if newSize > 2 ^ 32 - 1 || table.max.any (newSize > ·) then
        cont store (stack.push (.i32 0xFFFFFFFF))
      else
        let old := table.elems.size
        let table := { table with elems := table.elems ++ Array.replicate (i32 n).toNat r }
        cont (setTable store addr table) (stack.push (.i32 (UInt32.ofNat old)))
    | _, _ => .trap store (.host "table.grow: bad operands")
  | .table_fill t =>
    let (stack, idx, v, n) := pop3 stack
    match tableOf store inst t, v with
    | some (addr, table), .ref r =>
      let (i, n) := ((i32 idx).toNat, (i32 n).toNat)
      if i + n > table.elems.size then .trap store .outOfBoundsTableAccess
      else
        let elems := (List.range n).foldl (fun es k => es.set! (i + k) r) table.elems
        cont (setTable store addr { table with elems }) stack
    | _, _ => .trap store (.host "table.fill: bad operands")
  | .table_copy dstT srcT =>
    let (stack, d, s, n) := pop3 stack
    match tableOf store inst dstT, tableOf store inst srcT with
    | some (dstAddr, dst), some (_, src) =>
      let (d, s, n) := ((i32 d).toNat, (i32 s).toNat, (i32 n).toNat)
      if d + n > dst.elems.size || s + n > src.elems.size then .trap store .outOfBoundsTableAccess
      else
        let values := (List.range n).map fun k => src.elems[s + k]!
        let elems := (List.range n).foldl (fun es k => es.set! (d + k) values[k]!) dst.elems
        cont (setTable store dstAddr { dst with elems }) stack
    | _, _ => .trap store (.host "unknown table")
  | .table_init t e =>
    let (stack, d, s, n) := pop3 stack
    match tableOf store inst t, inst.elemAddrs[e]?.bind (store.elems[·]?) with
    | some (addr, table), some seg =>
      let (d, s, n) := ((i32 d).toNat, (i32 s).toNat, (i32 n).toNat)
      if d + n > table.elems.size || s + n > seg.elems.size then .trap store .outOfBoundsTableAccess
      else
        let elems := (List.range n).foldl (fun es k => es.set! (d + k) seg.elems[s + k]!)
          table.elems
        cont (setTable store addr { table with elems }) stack
    | _, _ => .trap store (.host "unknown table or segment")
  | .elem_drop e =>
    let addr := inst.elemAddrs[e]!
    cont { store with elems := store.elems.set! addr { elems := #[] } } stack
  | .load t packed arg =>
    let (stack, addr) := pop1 stack
    let len := match packed with
      | some p => p.bits / 8
      | none => t.byteWidth
    match loadNat store inst arg (i32 addr) len with
    | none => .trap store .outOfBoundsMemoryAccess
    | some raw =>
      let v : Value := match t, packed with
        | .i32, some p =>
          .i32 (UInt32.ofNat (if p.signed then Numeric.signExtend 32 p.bits raw else raw))
        | .i64, some p =>
          .i64 (UInt64.ofNat (if p.signed then Numeric.signExtend 64 p.bits raw else raw))
        | .i32, none => .i32 (UInt32.ofNat raw)
        | .i64, none => .i64 (UInt64.ofNat raw)
        | .f32, _ => .f32 (UInt32.ofNat raw)
        | .f64, _ => .f64 (UInt64.ofNat raw)
      cont store (stack.push v)
  | .store t bits arg =>
    let (stack, addr, v) := pop2 stack
    let len := match bits with
      | some b => b / 8
      | none => t.byteWidth
    let raw := match v with
      | .i32 n | .f32 n => n.toNat
      | .i64 n | .f64 n => n.toNat
      | .ref _ => 0
    storeEffect store inst arg (i32 addr) len raw (cont · stack)
  | .memory_size =>
    match store.memOf inst with
    | some mem => cont store (stack.push (.i32 (UInt32.ofNat mem.size)))
    | none => .trap store (.host "no memory")
  | .memory_grow =>
    let (stack, n) := pop1 stack
    match store.memOf inst with
    | none => .trap store (.host "no memory")
    | some mem =>
      match mem.grow (i32 n).toNat with
      | some mem' => cont (store.setMemOf inst mem') (stack.push (.i32 (UInt32.ofNat mem.size)))
      | none => cont store (stack.push (.i32 0xFFFFFFFF))
  | .memory_fill =>
    let (stack, d, v, n) := pop3 stack
    withMem stack labels rest locals fun mem =>
      mem.fill (i32 d).toNat (i32 n).toNat (UInt8.ofNat (i32 v).toNat)
  | .memory_copy =>
    let (stack, d, s, n) := pop3 stack
    withMem stack labels rest locals fun mem => mem.copy (i32 d).toNat (i32 s).toNat (i32 n).toNat
  | .memory_init x =>
    let (stack, d, s, n) := pop3 stack
    match inst.dataAddrs[x]?.bind (store.datas[·]?) with
    | none => .trap store (.host "unknown data segment")
    | some seg =>
      let (d, s, n) := ((i32 d).toNat, (i32 s).toNat, (i32 n).toNat)
      withMem stack labels rest locals fun mem =>
        if s + n > seg.bytes.size then none
        else mem.writeBytes d (seg.bytes.extract s (s + n))
  | .data_drop x =>
    let addr := inst.dataAddrs[x]!
    cont { store with datas := store.datas.set! addr { bytes := ByteArray.empty } } stack
  | .i32_const n => cont store (stack.push (.i32 n))
  | .i64_const n => cont store (stack.push (.i64 n))
  | .f32_const b => cont store (stack.push (.f32 b))
  | .f64_const b => cont store (stack.push (.f64 b))
  | .i32_eqz =>
    let (stack, a) := pop1 stack
    cont store (stack.push (.i32 (Numeric.bool (i32 a == 0))))
  | .i64_eqz =>
    let (stack, a) := pop1 stack
    let z := match a with | .i64 n => n == 0 | _ => false
    cont store (stack.push (.i32 (Numeric.bool z)))
  | .i32_unop op =>
    let (stack, a) := pop1 stack
    cont store (stack.push (.i32 (Numeric.iunop32 op (i32 a))))
  | .i64_unop op =>
    let (stack, a) := pop1 stack
    match a with
    | .i64 n => cont store (stack.push (.i64 (Numeric.iunop64 op n)))
    | _ => .trap store (.host "i64 operand expected")
  | .i32_binop op =>
    let (stack, a, b) := pop2 stack
    match Numeric.ibinop32 op (i32 a) (i32 b) with
    | .ok r => cont store (stack.push (.i32 r))
    | .error t => .trap store t
  | .i64_binop op =>
    let (stack, a, b) := pop2 stack
    match a, b with
    | .i64 x, .i64 y =>
      match Numeric.ibinop64 op x y with
      | .ok r => cont store (stack.push (.i64 r))
      | .error t => .trap store t
    | _, _ => .trap store (.host "i64 operands expected")
  | .i32_relop op =>
    let (stack, a, b) := pop2 stack
    cont store (stack.push (.i32 (Numeric.bool (Numeric.irelop32 op (i32 a) (i32 b)))))
  | .i64_relop op =>
    let (stack, a, b) := pop2 stack
    match a, b with
    | .i64 x, .i64 y => cont store (stack.push (.i32 (Numeric.bool (Numeric.irelop64 op x y))))
    | _, _ => .trap store (.host "i64 operands expected")
  | .f32_unop op =>
    let (stack, a) := pop1 stack
    match a with
    | .f32 x => cont store (stack.push (.f32 (Numeric.funop32 op x)))
    | _ => .trap store (.host "f32 operand expected")
  | .f64_unop op =>
    let (stack, a) := pop1 stack
    match a with
    | .f64 x => cont store (stack.push (.f64 (Numeric.funop64 op x)))
    | _ => .trap store (.host "f64 operand expected")
  | .f32_binop op =>
    let (stack, a, b) := pop2 stack
    match a, b with
    | .f32 x, .f32 y => cont store (stack.push (.f32 (Numeric.fbinop32 op x y)))
    | _, _ => .trap store (.host "f32 operands expected")
  | .f64_binop op =>
    let (stack, a, b) := pop2 stack
    match a, b with
    | .f64 x, .f64 y => cont store (stack.push (.f64 (Numeric.fbinop64 op x y)))
    | _, _ => .trap store (.host "f64 operands expected")
  | .f32_relop op =>
    let (stack, a, b) := pop2 stack
    match a, b with
    | .f32 x, .f32 y => cont store (stack.push (.i32 (Numeric.bool (Numeric.frelop32 op x y))))
    | _, _ => .trap store (.host "f32 operands expected")
  | .f64_relop op =>
    let (stack, a, b) := pop2 stack
    match a, b with
    | .f64 x, .f64 y => cont store (stack.push (.i32 (Numeric.bool (Numeric.frelop64 op x y))))
    | _, _ => .trap store (.host "f64 operands expected")
  | .cvt op =>
    let (stack, a) := pop1 stack
    match Numeric.cvt op a with
    | .ok v => cont store (stack.push v)
    | .error t => .trap store t

/-! ## Calls -/

/-- Commit a host call: its new host state, and the caller's memory if it
has one and the host returned it. -/
def commitHost (store : Store H) (callerInst : Option ModuleInst) (host : H)
    (mem : Option Memory) : Store H :=
  match callerInst, mem with
  | some inst, some m => ({ store with host := host } : Store H).setMemOf inst m
  | _, _ => { store with host := host }

/-- Enter the function at `addr` with its arguments on top of `stack`. A
host function runs to completion here; a Wasm function gets a new frame. -/
def enter (c : Config H) (stack : Array Value) (frames : List CallFrame) (addr : Nat) :
    StepResult H :=
  match c.store.funcs[addr]? with
  | none => .trap (.host "unknown function address") c.store
  | some (.host fn) =>
    let (stack, args) := popN stack fn.type.params.length
    -- The caller's memory, if there is a caller.
    let callerInst := frames.head?.bind fun f => c.store.modules[f.inst]?
    let mem := callerInst.bind c.store.memOf
    match fn.call c.store.host mem args with
    | .return values host mem' =>
      let store := commitHost c.store callerInst host mem'
      match frames with
      | [] => .done values store
      | _ =>
        let thread : Thread := { stack := stack ++ values.toArray, frames := frames }
        .next { c with store := store, thread := thread }
    | .trap reason host mem' => .trap reason (commitHost c.store callerInst host mem')
  | some (.wasm type inst code) =>
    if frames.length ≥ c.limits.maxCallDepth then .trap .callStackExhausted c.store
    else
      let (stack, args) := popN stack type.params.length
      let locals := args.toArray ++ (code.locals.map ValType.default).toArray
      let frame : CallFrame :=
        { locals := locals, inst := inst, arity := type.results.length,
          height := stack.size, labels := [], code := code.body }
      .next { c with thread := { stack := stack, frames := frame :: frames } }

/-- Leave the current frame with its results on top of the stack. -/
def leave (c : Config H) (store : Store H) (stack : Array Value) (frame : CallFrame)
    (frames : List CallFrame) : StepResult H :=
  let (stack, values) := popN stack frame.arity
  let stack := stack.shrink frame.height ++ values.toArray
  match frames with
  | [] => .done values store
  | _ => .next { c with store := store, thread := { stack := stack, frames := frames } }

/-- One step of the machine. -/
def step (c : Config H) : StepResult H :=
  match c.thread.frames with
  | [] => .done c.thread.stack.toList c.store
  | frame :: frames =>
    match frame.code, frame.labels with
    | [], [] => leave c c.store c.thread.stack frame frames
    | [], label :: labels =>
      let frame := { frame with labels := labels, code := label.rest }
      .next { c with thread := { c.thread with frames := frame :: frames } }
    | i :: rest, labels =>
      let inst := c.store.modules[frame.inst]!
      let eff := instr c.store inst frame.locals c.thread.stack labels i rest
      match eff.kind with
      | .continue stack labels code locals =>
        let frame := { frame with labels := labels, code := code, locals := locals }
        .next { c with store := eff.store, thread := { stack := stack, frames := frame :: frames } }
      | .call stack addr rest =>
        enter { c with store := eff.store } stack ({ frame with code := rest } :: frames) addr
      | .return stack => leave c eff.store stack frame frames
      | .trap reason => .trap reason eff.store

/-- `enter` reads only the store and the limits of its configuration. -/
theorem enter_congr {c c' : Config H} (hs : c.store = c'.store) (hl : c.limits = c'.limits)
    (stack : Array Value) (frames : List CallFrame) (addr : Nat) :
    enter c stack frames addr = enter c' stack frames addr := by
  rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
  cases hs; cases hl; rfl

/-- `leave` reads only the limits of its configuration. -/
theorem leave_congr {c c' : Config H} (hl : c.limits = c'.limits) (store : Store H)
    (stack : Array Value) (frame : CallFrame) (frames : List CallFrame) :
    leave c store stack frame frames = leave c' store stack frame frames := by
  rcases c with ⟨_, _, _⟩; rcases c' with ⟨_, _, _⟩
  cases hl; rfl

/-- `step` as it runs. `step` keeps its configuration alive while the
instruction executes (it rebuilds the result from it), so the store and the
operand stack are shared and every memory store or stack push copied them.
Taking the configuration apart first leaves them unshared. -/
def stepInPlace : Config H → StepResult H
  | ⟨store, ⟨stack, frames⟩, limits⟩ =>
    match frames with
    | [] => .done stack.toList store
    | frame :: frames =>
      match frame.code, frame.labels with
      | [], [] => leave ⟨store, ⟨#[], []⟩, limits⟩ store stack frame frames
      | [], label :: labels =>
        .next ⟨store, ⟨stack, { frame with labels := labels, code := label.rest } :: frames⟩, limits⟩
      | i :: rest, labels =>
        let inst := store.modules[frame.inst]!
        let eff := instr store inst frame.locals stack labels i rest
        match eff.kind with
        | .continue stack labels code locals =>
          let frame := { frame with labels := labels, code := code, locals := locals }
          .next ⟨eff.store, ⟨stack, frame :: frames⟩, limits⟩
        | .call stack addr rest =>
          enter ⟨eff.store, ⟨#[], []⟩, limits⟩ stack ({ frame with code := rest } :: frames) addr
        | .return stack => leave ⟨eff.store, ⟨#[], []⟩, limits⟩ eff.store stack frame frames
        | .trap reason => .trap reason eff.store

@[csimp] theorem step_eq_inPlace : @step = @stepInPlace := by
  funext H c
  rcases c with ⟨store, ⟨stack, frames⟩, limits⟩
  unfold step stepInPlace
  rcases frames with _ | ⟨frame, frames⟩
  · rfl
  · simp only
    split
    · exact leave_congr rfl _ _ _ _
    · rfl
    · split
      · rfl
      · exact enter_congr rfl rfl _ _ _
      · exact leave_congr rfl _ _ _ _
      · rfl

/-- Run up to `fuel` steps. -/
inductive RunResult (H : Type) where
  | done (values : List Value) (store : Store H)
  | trap (reason : Trap) (store : Store H)
  | outOfFuel (cfg : Config H)

def run (fuel : Nat) (c : Config H) : RunResult H :=
  match fuel with
  | 0 => .outOfFuel c
  | fuel + 1 =>
    match step c with
    | .next c => run fuel c
    | .done values store => .done values store
    | .trap reason store => .trap reason store

/-- Start a call of the function at `addr` with `args`. -/
def start (store : Store H) (limits : ExecLimits) (addr : Nat) (args : List Value) : StepResult H :=
  let c : Config H := { store := store, thread := { stack := #[], frames := [] }, limits := limits }
  enter c args.toArray [] addr

/-- Start a call of the Wasm function at `addr`: a frame push, no host call.
`none` if the address is a host function or unknown. -/
def startWasm (store : Store H) (limits : ExecLimits) (addr : Nat) (args : List Value) :
    Option (Config H) :=
  match store.funcs[addr]? with
  | some (.wasm type inst code) =>
    let locals := args.toArray ++ (code.locals.map ValType.default).toArray
    let frame : CallFrame :=
      { locals := locals, inst := inst, arity := type.results.length, height := 0, labels := [],
        code := code.body }
    some { store := store, thread := { stack := #[], frames := [frame] }, limits := limits }
  | _ => none

theorem startWasm_store {store : Store H} {limits : ExecLimits} {addr : Nat} {args : List Value}
    {c : Config H} (h : startWasm store limits addr args = some c) : c.store = store := by
  unfold startWasm at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · cases h

/-- Call a function to completion. -/
def invoke (store : Store H) (limits : ExecLimits) (fuel : Nat) (addr : Nat) (args : List Value) :
    RunResult H :=
  match start store limits addr args with
  | .next c => run fuel c
  | .done values store => .done values store
  | .trap reason store => .trap reason store

/-! ## The relation -/

/-- The proof-side step relation, defined from the executable `step`. -/
def Step (c c' : Config H) : Prop := step c = .next c'

/-- Zero or more steps. -/
inductive Steps : Config H → Config H → Prop where
  | refl (c : Config H) : Steps c c
  | tail {a b c : Config H} : Steps a b → Step b c → Steps a c

end Exec

end Wasm
