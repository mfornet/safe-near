import WasmLogic.Adequacy
import WasmLogic.Rules.Table
import Lean

/-!
# Rule coverage

A check, run when this file builds, that the logic has a rule for every
instruction of the runtime in scope. For each constructor of `Wasm.Instr`
the table below names the rules for it and Iris-Wasm's counterpart; the
check fails the build if

- a constructor is neither in the table nor listed as out of scope,
- a named rule does not exist, or
- a named rule's statement does not mention `wpi` and the constructor.

Every constructor is in scope: nearcore enables reference types and bulk
memory (`NearVM` validates with `Features.nearcore true`), so table and
bulk-memory instructions have rules too; Iris-Wasm, a Wasm 1.0 logic, has no
counterpart for them. The out-of-scope list stays, empty, for instructions a
future runtime adds before their rules exist.

The structural rules are checked to exist too.
-/

namespace WasmLogic.Coverage

open Lean Elab Command

/-- Rules for each instruction, with Iris-Wasm's counterpart. -/
def rules : List (Name × List Name × String) := [
  (``Wasm.Instr.unreachable, [``wpi_unreachable], "wp_unreachable"),
  (``Wasm.Instr.nop, [``wpi_nop], "wp_nop"),
  (``Wasm.Instr.block, [``wpi_block], "wp_block"),
  (``Wasm.Instr.loop, [``wpi_loop], "wp_loop"),
  (``Wasm.Instr.if, [``wpi_if_true, ``wpi_if_false], "wp_if_true, wp_if_false"),
  (``Wasm.Instr.br, [``wpi_br], "wp_br"),
  (``Wasm.Instr.br_if, [``wpi_br_if_true, ``wpi_br_if_false], "wp_br_if_true, wp_br_if_false"),
  (``Wasm.Instr.br_table, [``wpi_br_table], "wp_br_table"),
  (``Wasm.Instr.return, [``wpi_return], "wp_return"),
  (``Wasm.Instr.call, [``wpi_call, ``wpi_call_host, ``wpi_call_exhausted],
    "wp_call, wp_invoke_host; depth limit: none"),
  (``Wasm.Instr.call_indirect, [``wpi_call_indirect], "wp_call_indirect_success"),
  (``Wasm.Instr.ref_null, [``wpi_ref_null], "none (Wasm 1.0)"),
  (``Wasm.Instr.ref_is_null, [``wpi_ref_is_null], "none (Wasm 1.0)"),
  (``Wasm.Instr.ref_func, [``wpi_ref_func], "none (Wasm 1.0)"),
  (``Wasm.Instr.drop, [``wpi_drop], "wp_drop"),
  (``Wasm.Instr.select, [``wpi_select_true, ``wpi_select_false], "wp_select_true, wp_select_false"),
  (``Wasm.Instr.local_get, [``wpi_local_get], "wp_get_local"),
  (``Wasm.Instr.local_set, [``wpi_local_set], "wp_set_local"),
  (``Wasm.Instr.local_tee, [``wpi_local_tee], "wp_tee_local"),
  (``Wasm.Instr.global_get, [``wpi_global_get], "wp_get_global"),
  (``Wasm.Instr.global_set, [``wpi_global_set], "wp_set_global"),
  (``Wasm.Instr.load, [``wpi_load], "wp_load, wp_load_packed (one rule over widths)"),
  (``Wasm.Instr.store, [``wpi_store], "wp_store, wp_store_packed (one rule over widths)"),
  (``Wasm.Instr.memory_size, [``wpi_memory_size], "wp_current_memory"),
  (``Wasm.Instr.memory_grow, [``wpi_memory_grow, ``wpi_memory_grow_fail, ``wpi_memory_grow_either],
    "wp_grow_memory (its either-outcome shape is wpi_memory_grow_either)"),
  (``Wasm.Instr.i32_const, [``wpi_i32_const], "wp_val (constants are values there)"),
  (``Wasm.Instr.i64_const, [``wpi_i64_const], "wp_val"),
  (``Wasm.Instr.f32_const, [``wpi_f32_const], "wp_val"),
  (``Wasm.Instr.f64_const, [``wpi_f64_const], "wp_val"),
  (``Wasm.Instr.i32_eqz, [``wpi_i32_eqz], "wp_testop_i32"),
  (``Wasm.Instr.i64_eqz, [``wpi_i64_eqz], "wp_testop_i64"),
  (``Wasm.Instr.i32_unop, [``wpi_i32_unop], "wp_unop"),
  (``Wasm.Instr.i64_unop, [``wpi_i64_unop], "wp_unop"),
  (``Wasm.Instr.i32_binop, [``wpi_i32_binop, ``wpi_i32_binop_trap], "wp_binop, wp_binop_failure"),
  (``Wasm.Instr.i64_binop, [``wpi_i64_binop, ``wpi_i64_binop_trap], "wp_binop, wp_binop_failure"),
  (``Wasm.Instr.i32_relop, [``wpi_i32_relop], "wp_relop"),
  (``Wasm.Instr.i64_relop, [``wpi_i64_relop], "wp_relop"),
  (``Wasm.Instr.f32_unop, [``wpi_f32_unop], "wp_unop"),
  (``Wasm.Instr.f64_unop, [``wpi_f64_unop], "wp_unop"),
  (``Wasm.Instr.f32_binop, [``wpi_f32_binop], "wp_binop"),
  (``Wasm.Instr.f64_binop, [``wpi_f64_binop], "wp_binop"),
  (``Wasm.Instr.f32_relop, [``wpi_f32_relop], "wp_relop"),
  (``Wasm.Instr.f64_relop, [``wpi_f64_relop], "wp_relop"),
  (``Wasm.Instr.cvt, [``wpi_cvt, ``wpi_cvt_trap],
    "wp_cvtop_convert, wp_cvtop_convert_failure, wp_cvtop_reinterpret"),
  (``Wasm.Instr.table_get, [``wpi_table_get], "none (reference types)"),
  (``Wasm.Instr.table_set, [``wpi_table_set], "none (reference types)"),
  (``Wasm.Instr.table_size, [``wpi_table_size], "none (reference types)"),
  (``Wasm.Instr.table_grow, [``wpi_table_grow, ``wpi_table_grow_fail], "none (reference types)"),
  (``Wasm.Instr.table_fill, [``wpi_table_fill], "none (reference types)"),
  (``Wasm.Instr.table_copy, [``wpi_table_copy], "none (bulk memory)"),
  (``Wasm.Instr.table_init, [``wpi_table_init], "none (bulk memory)"),
  (``Wasm.Instr.elem_drop, [``wpi_elem_drop], "none (bulk memory)"),
  (``Wasm.Instr.memory_fill, [``wpi_memory_fill], "none (bulk memory)"),
  (``Wasm.Instr.memory_copy, [``wpi_memory_copy], "none (bulk memory)"),
  (``Wasm.Instr.memory_init, [``wpi_memory_init], "none (bulk memory)"),
  (``Wasm.Instr.data_drop, [``wpi_data_drop], "none (bulk memory)")]

/-- Constructors without rules, and why. -/
def outOfScope : List (Name × String) := []

/-- Structural rules, with Iris-Wasm's counterpart. -/
def structural : List (Name × String) := [
  (``wpi_seq, "wp_seq"),
  (``wpi_nil, "wp_nil"),
  (``wpi_wand, "wp_wand_ctx"),
  (``wpi_frame, "wp_frame_l (Iris's generic frame rule)"),
  (``wpInvoke_intro, "wp_invoke_native"),
  (``wpi_instr, "none: the generic rule every instruction rule is derived from"),
  (``wp_lift, "none: the one lifting lemma, over `Exec.step`"),
  (``wp_adequacy_cells, "wp_adequacy, with final-store facts from owned cells (wp_strong_adequacy)"),
  (``adequacy_cells, "wp_adequacy, instantiated to `Exec.run`: values, traps and final cells"),
  (``adequacy, "wp_adequacy, instantiated to `Exec.run`, pure postconditions")]

/-- Fails the build unless every instruction in scope has its rules. -/
elab "#check_rule_coverage" : command => do
  let env ← getEnv
  let some (.inductInfo ind) := env.find? ``Wasm.Instr
    | throwError "Wasm.Instr not found"
  let mut missing : Array Name := #[]
  for c in ind.ctors do
    match rules.find? (·.1 == c) with
    | some (_, names, _) =>
      for n in names do
        let some info := env.find? n
          | throwError "rule {n} for {c} does not exist"
        let used := info.type.getUsedConstants
        unless used.contains c do
          throwError "rule {n} does not mention {c}"
        unless used.contains ``wpi || used.contains ``wpInvoke do
          throwError "rule {n} is not a weakest-precondition rule"
    | none =>
      unless (outOfScope.find? (·.1 == c)).isSome do
        missing := missing.push c
  unless missing.isEmpty do
    throwError "no rule for {missing}"
  for (n, _) in structural do
    unless env.contains n do
      throwError "structural rule {n} does not exist"
  logInfo m!"rule coverage: {rules.length} instructions with rules, {outOfScope.length} out of scope"

#check_rule_coverage

end WasmLogic.Coverage
