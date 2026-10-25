import FastVMTests.Harness

/-!
# Random modules

Well-typed modules built from the instruction set: structured control with values, every integer operation with
edge-case operands, loads and stores around page and memory boundaries, bulk memory, calls (direct, indirect
with mismatches and null entries, recursive) and the NEAR host functions with random arguments. The validator
of the specification is the arbiter of well-formedness; a module it rejects is simply counted.
-/

namespace FastVMTests

open Wasm Wasm.Near NearFastVM

structure Env where
  locals : Array ValType
  /-- Function index space: imports then definitions. -/
  funcs : Array FuncType
  /-- Indices of the host functions among them. -/
  hosts : Array Nat
  globals : Array GlobalType
  types : Array FuncType
  tableSize : Nat
  results : List ValType
  /-- Branch arities of the enclosing labels, innermost first. -/
  labels : List (List ValType) := []
  /-- First of the four loop counters (i32 locals). -/
  counters : Nat
  loopDepth : Nat := 0
  /-- A function may call the ones after it only, so recursion is rare but the call graph is not a chain. -/
  self : Nat := 0

def edge32 : Array UInt32 :=
  #[0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 33, 63, 64, 100, 255, 256, 0x7f, 0x80, 0x7fff, 0x8000, 0xffff,
    0x10000, 0x7fffffff, 0x80000000, 0x80000001, 0xffffffff, 0xfffffffe, 0xdeadbeef, 0x01010101,
    0x55555555]

def edge64 : Array UInt64 :=
  #[0, 1, 2, 3, 63, 64, 65, 255, 256, 0xffff, 0x10000, 0xffffffff, 0x100000000, 0x7fffffff,
    0x80000000, 0x7fffffffffffffff, 0x8000000000000000, 0x8000000000000001, 0xffffffffffffffff,
    0xfffffffffffffffe, 0xdeadbeefcafebabe, 0x0101010101010101, 0x5555555555555555]

def addrs : Array UInt32 :=
  #[0, 1, 4, 8, 16, 64, 100, 255, 1000, 1024, 4096, 65520, 65528, 65531, 65532, 65533, 65534, 65535,
    65536, 65537, 131068, 131071, 131072, 67108856, 67108860, 67108863, 67108864, 67108865,
    0xfffffff8, 0xffffffff]

def genI32 : Gen UInt32 := do
  match ← below 5 with
  | 0 | 1 =>
    pick edge32
  | 2 =>
    return (← rand).toUInt32
  | 3 =>
    return (← below 64).toUInt32
  | _ =>
    pick addrs

def genI64 : Gen UInt64 := do
  match ← below 5 with
  | 0 | 1 =>
    pick edge64
  | 2 =>
    rand
  | 3 =>
    return (← below 64).toUInt64
  | _ =>
    return (← pick addrs).toUInt64

def smallAddr : Gen UInt32 := do
  match ← below 4 with
  | 0 =>
    pick addrs
  | _ =>
    return (← below 2000).toUInt32

def localsOf (env : Env) (t : ValType) : Array Nat :=
  (List.range env.locals.size).toArray.filter fun i => env.locals[i]! == t

def intTypes : Array ValType :=
  #[.i32, .i64]

def binops : Array IBinOp :=
  #[.add, .sub, .mul, .div_s, .div_u, .rem_s, .rem_u, .and, .or, .xor, .shl, .shr_s, .shr_u, .rotl,
    .rotr]

def relops : Array IRelOp :=
  #[.eq, .ne, .lt_s, .lt_u, .gt_s, .gt_u, .le_s, .le_u, .ge_s, .ge_u]

def unops32 : Array IUnOp :=
  #[.clz, .ctz, .popcnt, .extend8_s, .extend16_s]

def unops64 : Array IUnOp :=
  #[.clz, .ctz, .popcnt, .extend8_s, .extend16_s, .extend32_s]

def fbin : Array FBinOp :=
  #[.add, .sub, .mul, .div, .min, .max, .copysign]

def fun_ : Array FUnOp :=
  #[.abs, .neg, .ceil, .floor, .trunc, .nearest, .sqrt]

def frel : Array FRelOp :=
  #[.eq, .ne, .lt, .gt, .le, .ge]

def constOf : ValType → Gen Instr
  | .num .i32 => return .i32_const (← genI32)
  | .num .i64 => return .i64_const (← genI64)
  | .num .f32 => return .f32_const (← genI32)
  | .num .f64 => return .f64_const (← genI64)
  | .ref t => return .ref_null t

mutual
/-- Instructions that leave exactly one value of type `t`. -/
partial def genExpr (env : Env) (fuel : Nat) (t : ValType) : Gen (List Instr) := do
  let leaf : Gen (List Instr) := do
    let ls := localsOf env t
    match ← below 5 with
    | 0 | 1 =>
      return [← constOf t]
    | 2 | 3 =>
      if ls.isEmpty then
        return [← constOf t]
      else
        return [.local_get (← pick ls)]
    | _ =>
      let gs := (List.range env.globals.size).toArray.filter fun i => env.globals[i]!.type == t
      if gs.isEmpty then
        return [← constOf t]
      else
        return [.global_get (← pick gs)]
  if fuel == 0 then
    return ← leaf
  let f := fuel - 1
  match t with
  | .num .i32 =>
    match ← below 22 with
    | 0 | 1 =>
      leaf
    | 2 =>
      return (← genExpr env f .i32) ++ [.i32_unop (← pick unops32)]
    | 3 =>
      return (← genExpr env f .i32) ++ [.i32_eqz]
    | 4 =>
      return (← genExpr env f .i64) ++ [.i64_eqz]
    | 5 | 6 | 7 =>
      return (← genExpr env f .i32) ++ (← genExpr env f .i32) ++ [.i32_binop (← pick binops)]
    | 8 | 9 =>
      return (← genExpr env f .i32) ++ (← genExpr env f .i32) ++ [.i32_relop (← pick relops)]
    | 10 =>
      return (← genExpr env f .i64) ++ (← genExpr env f .i64) ++ [.i64_relop (← pick relops)]
    | 11 =>
      return (← genExpr env f .i64) ++ [.cvt .i32_wrap_i64]
    | 12 | 13 =>
      genLoad env f .i32
    | 14 =>
      genCall env f t
    | 15 =>
      genSelect env f t
    | 16 =>
      genIf env f t
    | 17 =>
      genBlockBr env f t
    | 18 =>
      genTee env f t
    | 19 =>
      match ← below 4 with
      | 0 =>
        return [.memory_size]
      | 1 =>
        return (← genExpr env 0 .i32) ++ [.memory_grow]
      | 2 =>
        return (← genExpr env f .f64) ++ (← genExpr env f .f64) ++ [.f64_relop (← pick frel)]
      | _ =>
        return (← genExpr env f .f32) ++ [.cvt .i32_reinterpret_f32]
    | 20 =>
      genCallIndirect env f t
    | _ =>
      match ← below 3 with
      | 0 =>
        return (← genExpr env f .f64) ++
            [.cvt
                (←
                  pick
                      #[.i32_trunc_f64_s, .i32_trunc_f64_u, .i32_trunc_sat_f64_s,
                        .i32_trunc_sat_f64_u])]
      | 1 =>
        return (← genExpr env f .f32) ++
            [.cvt
                (←
                  pick
                      #[.i32_trunc_f32_s, .i32_trunc_f32_u, .i32_trunc_sat_f32_s,
                        .i32_trunc_sat_f32_u])]
      | _ =>
        genHostCall env f t
  | .num .i64 =>
    match ← below 20 with
    | 0 | 1 =>
      leaf
    | 2 =>
      return (← genExpr env f .i64) ++ [.i64_unop (← pick unops64)]
    | 3 | 4 | 5 | 6 =>
      return (← genExpr env f .i64) ++ (← genExpr env f .i64) ++ [.i64_binop (← pick binops)]
    | 7 =>
      return (← genExpr env f .i32) ++ [.cvt (← pick #[.i64_extend_i32_s, .i64_extend_i32_u])]
    | 8 | 9 =>
      genLoad env f .i64
    | 10 =>
      genCall env f t
    | 11 =>
      genSelect env f t
    | 12 =>
      genIf env f t
    | 13 =>
      genBlockBr env f t
    | 14 =>
      genTee env f t
    | 15 =>
      genHostCall env f t
    | 16 =>
      genCallIndirect env f t
    | 17 =>
      return (← genExpr env f .f64) ++
          [.cvt
              (←
                pick
                    #[.i64_trunc_f64_s, .i64_trunc_f64_u, .i64_trunc_sat_f64_s,
                      .i64_trunc_sat_f64_u, .i64_reinterpret_f64])]
    | 18 =>
      return (← genExpr env f .f32) ++
          [.cvt
              (←
                pick
                    #[.i64_trunc_f32_s, .i64_trunc_f32_u, .i64_trunc_sat_f32_s,
                      .i64_trunc_sat_f32_u])]
    | _ =>
      return (← genExpr env f .i64) ++ (← genExpr env f .i32) ++
          [.cvt .i64_extend_i32_u, .i64_binop (← pick binops)]
  | .num .f32 =>
    match ← below 8 with
    | 0 | 1 =>
      leaf
    | 2 =>
      return (← genExpr env f .f32) ++ [.f32_unop (← pick fun_)]
    | 3 | 4 =>
      return (← genExpr env f .f32) ++ (← genExpr env f .f32) ++ [.f32_binop (← pick fbin)]
    | 5 =>
      return (← genExpr env f .i32) ++
          [.cvt (← pick #[.f32_convert_i32_s, .f32_convert_i32_u, .f32_reinterpret_i32])]
    | 6 =>
      return (← genExpr env f .i64) ++ [.cvt (← pick #[.f32_convert_i64_s, .f32_convert_i64_u])]
    | _ =>
      return (← genExpr env f .f64) ++ [.cvt .f32_demote_f64]
  | .num .f64 =>
    match ← below 8 with
    | 0 | 1 =>
      leaf
    | 2 =>
      return (← genExpr env f .f64) ++ [.f64_unop (← pick fun_)]
    | 3 | 4 =>
      return (← genExpr env f .f64) ++ (← genExpr env f .f64) ++ [.f64_binop (← pick fbin)]
    | 5 =>
      return (← genExpr env f .i32) ++ [.cvt (← pick #[.f64_convert_i32_s, .f64_convert_i32_u])]
    | 6 =>
      return (← genExpr env f .i64) ++
          [.cvt (← pick #[.f64_convert_i64_s, .f64_convert_i64_u, .f64_reinterpret_i64])]
    | _ =>
      return (← genExpr env f .f32) ++ [.cvt .f64_promote_f32]
  | .ref _ =>
    leaf
partial def genLoad (env : Env) (f : Nat) (t : ValType) : Gen (List Instr) := do
  let addr ←
    match ← below 3 with
    | 0 =>
      genExpr env f .i32
    | _ =>
      return [.i32_const (← smallAddr)]
  let off ←
    match ← below 4 with
    | 0 =>
      pure (← pick #[0, 1, 2, 3, 4, 7, 8, 65535, 65536, 0xffffffff])
    | _ =>
      pure 0
  let arg : MemArg := { align := 0, offset := off }
  let ld ←
    match t with
    | .num .i32 =>
      match ← below 5 with
      | 0 =>
        pure (Instr.load .i32 (some ⟨8, false⟩) arg)
      | 1 =>
        pure (Instr.load .i32 (some ⟨8, true⟩) arg)
      | 2 =>
        pure (Instr.load .i32 (some ⟨16, false⟩) arg)
      | 3 =>
        pure (Instr.load .i32 (some ⟨16, true⟩) arg)
      | _ =>
        pure (Instr.load .i32 none arg)
    | _ =>
      match ← below 8 with
      | 0 =>
        pure (Instr.load .i64 (some ⟨8, false⟩) arg)
      | 1 =>
        pure (Instr.load .i64 (some ⟨8, true⟩) arg)
      | 2 =>
        pure (Instr.load .i64 (some ⟨16, false⟩) arg)
      | 3 =>
        pure (Instr.load .i64 (some ⟨16, true⟩) arg)
      | 4 =>
        pure (Instr.load .i64 (some ⟨32, false⟩) arg)
      | 5 =>
        pure (Instr.load .i64 (some ⟨32, true⟩) arg)
      | _ =>
        pure (Instr.load .i64 none arg)
  return addr ++ [ld]
partial def genCall (env : Env) (f : Nat) (t : ValType) : Gen (List Instr) := do
  let cands :=
    (List.range env.funcs.size).toArray.filter fun i =>
      env.funcs[i]!.results == [t] && !env.hosts.contains i
  if cands.isEmpty then
    return [← constOf t]
  let i ← pick cands
  let mut out : List Instr := []
  for p in env.funcs[i]!.params do
    out := out ++ (← genExpr env (f / 2) p)
  return out ++ [.call i]
partial def genHostCall (env : Env) (f : Nat) (t : ValType) : Gen (List Instr) := do
  let cands := env.hosts.filter fun i => env.funcs[i]!.results == [t]
  if cands.isEmpty then
    return [← constOf t]
  let i ← pick cands
  let mut out : List Instr := []
  for p in env.funcs[i]!.params do
    let e ←
      match p with
      | .num .i64 =>
        do
          match ← below 3 with
          | 0 =>
            genExpr env 0 p
          | _ =>
            pure [Instr.i64_const (← smallAddr).toUInt64]
      | _ =>
        genExpr env 0 p
    out := out ++ e
  return out ++ [.call i]
partial def genSelect (env : Env) (f : Nat) (t : ValType) : Gen (List Instr) := do
  return (← genExpr env f t) ++ (← genExpr env f t) ++ (← genExpr env f .i32) ++ [.select none]
partial def genIf (env : Env) (f : Nat) (t : ValType) : Gen (List Instr) := do
  let env' := { env with labels := [t] :: env.labels }
  return (← genExpr env f .i32) ++
      [.«if» (.val t) ((← genStmts env' f 2) ++ (← genExpr env' f t))
          ((← genStmts env' f 2) ++ (← genExpr env' f t))]
/-- A block with a result whose value a `br_if` out of the block may carry. -/
partial def genBlockBr (env : Env) (f : Nat) (t : ValType) : Gen (List Instr) := do
  let env' := { env with labels := [t] :: env.labels }
  let inner :=
    (← genStmts env' f 2) ++ (← genExpr env' f t) ++ (← genExpr env' f .i32) ++ [.br_if 0]
  if (← chance 1 2) then
    let more ← genExpr env' f t
    return [.block (.val t) (inner ++ [.drop] ++ more)]
  else
    return [.block (.val t) inner]
partial def genTee (env : Env) (f : Nat) (t : ValType) : Gen (List Instr) := do
  let ls := localsOf env t
  if ls.isEmpty then
    return ← genExpr env f t
  return (← genExpr env f t) ++ [.local_tee (← pick ls)]
partial def genCallIndirect (env : Env) (f : Nat) (t : ValType) : Gen (List Instr) := do
  let cands := (List.range env.types.size).toArray.filter fun i => env.types[i]!.results == [t]
  if cands.isEmpty || env.tableSize == 0 then
    return [← constOf t]
  let ti ← pick cands
  let mut out : List Instr := []
  for p in env.types[ti]!.params do
    out := out ++ (← genExpr env (f / 2) p)
  let idx ←
    match ← below 4 with
    | 0 =>
      pure [Instr.i32_const (← genI32)]
    | _ =>
      pure [Instr.i32_const (← below (env.tableSize + 2)).toUInt32]
  return out ++ idx ++ [.call_indirect ti 0]
partial def genStmts (env : Env) (f : Nat) (n : Nat) : Gen (List Instr) := do
  let mut out : List Instr := []
  for _ in [0:← below (n + 1)] do
    out := out ++ (← genStmt env f)
  return out
/-- Instructions with no net effect on the stack. -/
partial def genStmt (env : Env) (f : Nat) : Gen (List Instr) := do
  let f := if f == 0 then 0 else f - 1
  match ← below 24 with
  | 0 | 1 | 2 =>
    let t ← pick intTypes
    let ls := localsOf env t
    if ls.isEmpty then
      return []
    else
      return (← genExpr env f t) ++ [.local_set (← pick ls)]
  | 3 =>
    let gs := (List.range env.globals.size).toArray.filter fun i => env.globals[i]!.mutable
    if gs.isEmpty then
      return []
    else
      let g ← pick gs
      return (← genExpr env f env.globals[g]!.type) ++ [.global_set g]
  | 4 | 5 | 6 =>
    let addr ←
      match ← below 3 with
      | 0 =>
        genExpr env f .i32
      | _ =>
        pure [Instr.i32_const (← smallAddr)]
    let off ← pick #[0, 0, 0, 1, 4, 8, 65535, 65532]
    let arg : MemArg := { align := 0, offset := off }
    match ← below 6 with
    | 0 =>
      return addr ++ (← genExpr env f .i32) ++ [.store .i32 (some 8) arg]
    | 1 =>
      return addr ++ (← genExpr env f .i32) ++ [.store .i32 (some 16) arg]
    | 2 =>
      return addr ++ (← genExpr env f .i32) ++ [.store .i32 none arg]
    | 3 =>
      return addr ++ (← genExpr env f .i64) ++ [.store .i64 none arg]
    | 4 =>
      return addr ++ (← genExpr env f .i64) ++ [.store .i64 (some (← pick #[8, 16, 32])) arg]
    | _ =>
      return addr ++ (← genExpr env f .i32) ++ [.store .i32 (some 8) arg]
  | 7 =>
    let t ← pick intTypes
    return (← genExpr env f t) ++ [.drop]
  | 8 | 9 =>
    let cands :=
      (List.range env.funcs.size).toArray.filter fun i =>
        env.funcs[i]!.results == [] && !env.hosts.contains i
    if cands.isEmpty then
      return []
    else
      let i ← pick cands
      let mut out : List Instr := []
      for p in env.funcs[i]!.params do
        out := out ++ (← genExpr env (f / 2) p)
      return out ++ [.call i]
  | 10 | 11 =>
    -- a host call whose results are dropped
    if env.hosts.isEmpty then
      return []
    else
      let i ← pick env.hosts
      let ft := env.funcs[i]!
      let mut out : List Instr := []
      for p in ft.params do
        let e ←
          match p with
          | .num .i64 =>
            do
              match ← below 3 with
              | 0 =>
                genExpr env 0 p
              | _ =>
                pure [Instr.i64_const (← smallAddr).toUInt64]
          | _ =>
            genExpr env 0 p
        out := out ++ e
      return out ++ [.call i] ++ ft.results.map (fun _ => Instr.drop)
  | 12 =>
    let env' := { env with labels := [] :: env.labels }
    return (← genExpr env f .i32) ++ [.«if» .empty (← genStmts env' f 3) (← genStmts env' f 3)]
  | 13 =>
    let env' := { env with labels := [] :: env.labels }
    let body :=
      (← genStmts env' f 3) ++ (← genExpr env' f .i32) ++ [.br_if 0] ++ (← genStmts env' f 2)
    return [.block .empty body]
  | 14 | 15 =>
    -- a loop with a counter: runs a few times unless the body breaks out
    if env.loopDepth ≥ 3 then
      return []
    else
      let c := env.counters + env.loopDepth
      let env' :=
        { env with
          labels := [] :: env.labels, loopDepth := env.loopDepth + 1 }
      let iters ← below 6
      let back ←
        match ← below 12 with
        | 0 =>
          pure [Instr.br 0]
        | 1 =>
          pure ((← genExpr env' f .i32) ++ [.br_if 0])
        | _ =>
          pure [Instr.local_get c, .i32_const 1, .i32_binop .sub, .local_tee c, .br_if 0]
      return [.i32_const iters.toUInt32, .local_set c, .loop .empty ((← genStmts env' f 4) ++ back)]
  | 16 =>
    match env.labels with
    | [] =>
      return []
    | _ =>
      let l ← below env.labels.length
      let ts := env.labels[l]!
      let mut out : List Instr := []
      for t in ts do
        out := out ++ (← genExpr env f t)
      return out ++ (← genExpr env f .i32) ++ [.br_if l] ++ ts.map (fun _ => Instr.drop)
  | 17 =>
    -- br_table over nested blocks
    let n ← below 3
    let env' := { env with labels := (List.replicate (n + 1) []) ++ env.labels }
    let labels := (List.range (n + 1)).map fun _ => 0
    let ls ← (List.range (n + 1)).mapM fun _ => below (n + 1 + env.labels.length)
    let _ := labels
    let ls := ls.filter fun l => (env'.labels[l]? == some [])
    let d := (← below (n + 1))
    let core := (← genExpr env' f .i32) ++ [.br_table ls d]
    let mut body := core
    for _ in [0:n + 1] do
      body := [.block .empty (body ++ (← genStmts env' 1 1))]
    return body
  | 18 =>
    return (← genExpr env f .i32) ++ (← genExpr env f .i32) ++ (← genExpr env f .i32) ++
        [.memory_fill]
  | 19 =>
    return (← genExpr env f .i32) ++ (← genExpr env f .i32) ++ (← genExpr env f .i32) ++
        [.memory_copy]
  | 20 =>
    match ← below 6 with
    | 0 =>
      return [.unreachable]
    | 1 =>
      return (← genExprs env f env.results) ++ [.«return»]
    | _ =>
      return []
  | 21 =>
    let t ← pick #[ValType.f32, .f64]
    let ls := localsOf env t
    if ls.isEmpty then
      return []
    else
      return (← genExpr env f t) ++ [.local_set (← pick ls)]
  | 22 =>
    -- small fill / copy with in-range arguments
    let d ← smallAddr
    let s ← smallAddr
    let n ← below 300
    match ← below 2 with
    | 0 =>
      return [.i32_const d, .i32_const (← genI32), .i32_const n.toUInt32, .memory_fill]
    | _ =>
      return [.i32_const d, .i32_const s, .i32_const n.toUInt32, .memory_copy]
  | _ =>
    return []
partial def genExprs (env : Env) (f : Nat) (ts : List ValType) : Gen (List Instr) := do
  let mut out : List Instr := []
  for t in ts do
    out := out ++ (← genExpr env f t)
  return out
end

end FastVMTests
