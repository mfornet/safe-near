import FastVMTests.Gen

/-!
# Random modules, assembled

A module with a memory, a table, globals, data, a few host imports and a few functions; `main` (type `[] -> []`)
is the only export. Calls reach every function, indirect calls reach those listed in the table.
-/

namespace FastVMTests

open Wasm Wasm.Near NearFastVM

def sigs : Array FuncType :=
  #[{ params := [], results := [] }, { params := [.i32], results := [.i32] },
    { params := [.i64], results := [.i64] }, { params := [.i32, .i32], results := [.i32] },
    { params := [.i64, .i64], results := [.i64] }, { params := [.i32, .i64], results := [.i32] },
    { params := [.i32], results := [] }, { params := [], results := [.i32] },
    { params := [], results := [.i64] }, { params := [.i64], results := [.i32] },
    { params := [.i32, .i32], results := [] }]

/-- Host functions that are cheap to call with arbitrary arguments and observable in the outcome. -/
def hostNames : Array String :=
  #["input", "register_len", "read_register", "write_register", "log_utf8", "log_utf16", "abort",
    "value_return", "storage_write", "storage_read", "storage_has_key", "storage_remove",
    "used_gas", "prepaid_gas", "block_index", "block_timestamp", "epoch_height", "storage_usage",
    "account_balance", "attached_deposit", "random_seed", "current_account_id", "signer_account_id",
    "predecessor_account_id", "panic", "panic_utf8", "gas", "promise_batch_create",
    "promise_batch_action_transfer", "promise_return", "promise_results_count",
    "validator_total_stake", "sha256", "keccak256"]

def stringBytes (s : String) : ByteArray :=
  s.toUTF8

/-- A random module. `hosts` is `meteredHostFns` of the configuration. -/
instance : Inhabited (ImportDecl × NearHostFn NearState) :=
  ⟨(default, { invoke := fun _ _ => .Return [] ⟨default, default⟩ })⟩

def genModule (hosts : List (ImportDecl × NearHostFn NearState)) : Gen Module := do
  let hostPool := hosts.toArray.filter fun (d, _) => hostNames.contains d.name
  let nImp ← below 5
  let mut imports : Array Import := #[]
  let mut types := sigs
  let mut funcs : Array FuncType := #[]
  let mut hostIdx : Array Nat := #[]
  for k in [0:nImp] do
    let (d, _) ← pick hostPool
    let ft : FuncType := { params := d.params, results := d.results }
    let ti := types.size
    types := types.push ft
    imports := imports.push { «module» := d.module, name := d.name, desc := .func ti }
    funcs := funcs.push ft
    hostIdx := hostIdx.push k
  let nDef := 2 + (← below 4)
  -- function types: main first
  let mut defTypes : Array Nat := #[0]
  for _ in [1:nDef] do
    defTypes := defTypes.push (← below sigs.size)
  for ti in defTypes do
    funcs := funcs.push types[ti]!
  let nGlobals := 1 + (← below 3)
  let mut globals : Array Global := #[]
  for _ in [0:nGlobals] do
    let t ← pick intTypes
    let a ← genI32
    let b ← genI64
    let init : Instr := if t == .i32 then .i32_const a else .i64_const b
    globals := globals.push { type := { type := t, mutable := true }, init := [init] }
  globals := globals.push { type := { type := .i32, mutable := false }, init := [.i32_const 42] }
  let gtypes := globals.map (·.type)
  let tableSize := nDef + 2
  let mut inTable : Array Nat := #[]
  for k in [0:nDef] do
    if ← chance 2 3 then
      inTable := inTable.push (nImp + k)
  let mut defs : Array Func := #[]
  for k in [0:nDef] do
    let ft := types[defTypes[k]!]!
    let nExtra ← below 4
    let mut locals : List ValType := [.i32, .i32, .i32, .i32]
    for _ in [0:nExtra] do
      locals := locals ++ [← pick #[ValType.i32, .i64, .i64, .f32, .f64]]
    let env : Env :=
      { locals := (ft.params ++ locals).toArray, funcs, hosts := hostIdx, globals := gtypes, types,
        tableSize, results := ft.results, counters := ft.params.length, self := nImp + k }
    let fuel := 2 + (← below 3)
    let body := (← genStmts env fuel 5) ++ (← genExprs env fuel ft.results)
    defs := defs.push { type := defTypes[k]!, locals, body }
  let data1 := stringBytes "hello fast vm " ++ ⟨#[0, 1, 2, 255]⟩
  return { types, funcs := defs, imports,
           tables :=
             #[{ type := { elem := .funcref, limits := { min := tableSize, max := none } } }],
           mems := #[{ type := { limits := { min := 1, max := none } } }], globals,
           elems :=
             #[{ type := .funcref, init := (inTable.map fun f => [Instr.ref_func f]).toList,
                 mode := .active 0 [.i32_const 0] }],
           datas :=
             #[{ init := data1, mode := .active 0 [.i32_const 0] },
               { init := ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩, mode := .active 0 [.i32_const 65532] }],
           exports := #[{ name := "main", desc := .func nImp }] }

end FastVMTests
