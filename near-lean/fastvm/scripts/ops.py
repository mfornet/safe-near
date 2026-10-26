"""The operation table of the fast engine, shared by the generators of `NearFastVM/Ops.lean` and `Exec.lean`.

Every integer operation of the MVP has an operation of its own, so that the interpreter dispatches once per
Wasm instruction. Floating-point operations, truncations and conversions go through `Op.cold`, which keeps the
original instruction and runs it with `Wasm.Numeric`.
"""

I_BIN = ["add", "sub", "mul", "div_s", "div_u", "rem_s", "rem_u", "and", "or", "xor", "shl", "shr_s", "shr_u",
         "rotl", "rotr"]
I_REL = ["eq", "ne", "lt_s", "lt_u", "gt_s", "gt_u", "le_s", "le_u", "ge_s", "ge_u"]
I_UN32 = ["clz", "ctz", "popcnt", "extend8_s", "extend16_s"]
I_UN64 = ["clz", "ctz", "popcnt", "extend8_s", "extend16_s"]  # extend32_s is i64_extend_i32_s

CONTROL = ["unreachable", "nop", "jmp", "br", "br_if", "if_z", "br_table", "ret", "call",
           "call_indirect", "select", "local_get", "local_set", "local_tee", "global_get", "global_set",
           "const", "ld32", "ld64", "ld8u", "ld8s32", "ld8s64", "ld16u", "ld16s32", "ld16s64", "ld32s64",
           "st8", "st16", "st32", "st64", "memory_size", "memory_grow", "memory_fill", "memory_copy",
           "i32_wrap_i64", "i64_extend_i32_s", "i64_extend_i32_u", "i32_eqz", "i64_eqz", "cold"]


def numeric_ops():
    ops = []
    for w in ("i32", "i64"):
        ops += [f"{w}_{o}" for o in I_BIN]
        ops += [f"{w}_{o}" for o in I_REL]
    ops += [f"i32_{o}" for o in I_UN32]
    ops += [f"i64_{o}" for o in I_UN64]
    return ops


def all_ops():
    return CONTROL + numeric_ops()
