#!/usr/bin/env python3
"""Generate NearFastVM/Exec.lean: the interpreter loop, one arm per operation.

Slots are pairs of 32-bit words (`NearFastVM.ExecCore`): the second operand of an instruction is at `i + 2`, the
third at `i + 4`; an `i32` result is written to the low word only.
"""
import pathlib
from ops import I_BIN, I_REL, I_UN32, I_UN64

ORDER = ["fns", "fc", "fid", "pc", "fp", "st", "gl", "pg", "fr", "depth", "host", "acc", "lim"]
DEFAULT = dict(fns="fns", fc="fc", fid="fid", pc="(pc + 1)", fp="fp", st="st", gl="gl", pg="pg", fr="fr",
               depth="depth", host="host", acc="acc", lim="lim")


def k(**kw):
    a = dict(DEFAULT)
    a.update(kw)
    return "loop cx " + " ".join(a[n] for n in ORDER)


def trap(t, acc="acc"):
    return f"finish host {acc} pg gl (.trap {t})"


arms = []


def arm(op, body):
    body = body.strip("\n")
    if "match" in body:
        body = "(" + body + ")"
    lines = body.split("\n")
    arms.append(f"  | .{op} =>\n" + "\n".join("    " + l if l.strip() else l for l in lines))


def indent(text, n):
    pad = " " * n
    return "\n".join(pad + l if l.strip() else l for l in text.strip("\n").split("\n"))


arm("unreachable", trap(".unreachable"))
arm("nop", k())
arm("jmp", k(pc="ins.y.toUSize"))
arm("br", f"""
let st := if ins.z == 0 then st else moveSlots st i (fp + ins.w.toUSize) ins.z.toNat
{k(pc="ins.y.toUSize", st="st")}""")
arm("br_if", f"""
let c := rd32 st (fp + ins.imm.toUSize)
if c == 0 then {k()} else
let acc1 := acc + ins.cost2
if acc1 > lim then gasFail host acc ins.cost2.toNat pg gl else
let st := if ins.z == 0 then st else moveSlots st i (fp + ins.w.toUSize) ins.z.toNat
{k(pc="ins.y.toUSize", st="st", acc="acc1")}""")
arm("if_z", f"""
if rd32 st i == 0 then {k(pc="ins.y.toUSize")} else {k()}""")
arm("br_table", f"""
let idx := (rd32 st i).toNat
let entries := fc.tables[ins.imm.toNat]!
let e := if idx + 1 < entries.size then entries[idx]! else entries[entries.size - 1]!
let acc1 := acc + e.cost2
if acc1 > lim then gasFail host acc e.cost2.toNat pg gl else
let st := if e.z == 0 then st else moveSlots st (fp + e.x.toUSize) (fp + e.w.toUSize) e.z.toNat
{k(pc="e.y.toUSize", st="st", acc="acc1")}""")

arm("ret", f"""
let n := ins.z.toNat
let st := if n == 0 || i == fp then st else moveSlots st i fp n
if depth == 1 then finish host acc pg gl (.done (resultsOf st fc.results fp)) else
let ri := (depth.toNat - 2) * 3
let fid' := fr[ri + 1]!.toNat
match fns[fid']! with
| some fc' => {k(fc="fc'", fid="fid'", pc="fr[ri]!.toUInt64.toUSize", fp="fr[ri + 2]!.toUInt64.toUSize", depth="(depth - 1)")}
| none => finish host acc pg gl .unsupported""")


def call_body(addr, base):
    """The call of the function at store address `addr` whose arguments start at word `base`."""
    return f"""
match cx.funcs[{addr}]! with
| .host fn =>
  let r := callHost cx fn {base} st pg host acc
  if r.dropped then finish r.host 0 #[] gl .unsupported else
  match r.trap with
  | some t => finish r.host 0 r.pg gl (.trap t)
  | none => {k(st="r.st", pg="r.pg", host="r.host", acc="0", lim="r.lim")}
| .wasm ty ii code =>
  if ii != cx.instIdx then finish host acc pg gl .unsupported else
  if depth.toNat ≥ cx.maxDepth then {trap(".callStackExhausted")} else
  let (fns, callee?) :=
    match fns[{addr}]! with
    | some c => (fns, some c)
    | none =>
      match compileFunc cx ty code with
      | some c => (fns.set! {addr} (some c), some c)
      | none => (fns, none)
  match callee? with
  | none => finish host acc pg gl .unsupported
  | some callee =>
    let acc1 := acc + callee.activation.toUInt64
    if acc1 > lim then gasFail host acc callee.activation pg gl else
    let newFp := {base}
    let need := newFp.toNat + callee.frameSlots
    let st := if need > st.size then growStack st need else st
    let st := zeroSlots st (newFp + callee.nparams.toUSize * 2) (callee.nlocals - callee.nparams)
    let ri := (depth.toNat - 1) * 3
    let fr := if ri < fr.size then ((fr.set! ri (pc + 1).toUInt64.toUInt32).set! (ri + 1) fid.toUInt32).set! (ri + 2) fp.toUInt64.toUInt32
      else ((fr.push (pc + 1).toUInt64.toUInt32).push fid.toUInt32).push fp.toUInt64.toUInt32
    {k(fns="fns", fc="callee", fid=addr, pc="0", fp="newFp", st="st", fr="fr", depth="(depth + 1)", acc="acc1")}"""


arm("call", f"""
let addr := ins.imm.toNat
{call_body("addr", "i")}""")
arm("call_indirect", f"""
let idx := (rd32 st i).toNat
let table := cx.tables[cx.inst.tableAddrs[ins.w.toNat]!]!
match table.elems[idx]? with
| none => {trap(".undefinedElement")}
| some (.null _) => {trap(".uninitializedElement")}
| some (.extern _) => {trap(".indirectCallTypeMismatch")}
| some (.func addr) =>
  match cx.funcs[addr]? with
  | none => {trap('(.host "dangling function reference")')}
  | some fn =>
    if fn.type == cx.inst.types[ins.y.toNat]! then (
{indent(call_body("addr", "(i - ins.z.toUSize * 2)"), 6)})
    else {trap(".indirectCallTypeMismatch")}""")

arm("select", f"""
if rd32 st (i + 4) != 0 then {k()} else {k(st="(wr st i (rd st (i + 2)))")}""")
arm("local_get", k(st="(wr st i (rd st (fp + ins.y.toUSize)))"))
arm("local_set", k(st="(wr st (fp + ins.y.toUSize) (rd st i))"))
arm("local_tee", k(st="(wr st (fp + ins.y.toUSize) (rd st i))"))
arm("global_get", k(st="(wr st i (rd gl ins.y.toUSize))"))
arm("global_set", k(gl="(wr gl ins.y.toUSize (rd st i))"))
arm("const", k(st="(wr st i ins.imm)"))

oob = trap(".outOfBoundsMemoryAccess")


def load(op, n, conv):
    arm(op, f"""
let ea := (rd32 st i).toUInt64 + ins.imm
if ea + ({n} : UInt64) > ((pg.size.toUInt64) <<< (16 : UInt64)) then {oob} else
let v := readN pg ea {n}
{k(st=f"(wr st i ({conv}))")}""")


load("ld32", 4, "v")
load("ld64", 8, "v")
load("ld8u", 1, "v")
load("ld16u", 2, "v")
load("ld8s32", 1, "v.toUInt8.toInt8.toInt32.toUInt32.toUInt64")
load("ld8s64", 1, "v.toUInt8.toInt8.toInt64.toUInt64")
load("ld16s32", 2, "v.toUInt16.toInt16.toInt32.toUInt32.toUInt64")
load("ld16s64", 2, "v.toUInt16.toInt16.toInt64.toUInt64")
load("ld32s64", 4, "v.toUInt32.toInt32.toInt64.toUInt64")


def store(op, n):
    arm(op, f"""
let ea := (rd32 st i).toUInt64 + ins.imm
if ea + ({n} : UInt64) > ((pg.size.toUInt64) <<< (16 : UInt64)) then {oob} else
{k(pg=f"(writeN pg ea {n} (rd st (i + 2)))")}""")


store("st8", 1)
store("st16", 2)
store("st32", 4)
store("st64", 8)

arm("memory_size", k(st="(wr32 st i pg.size.toUInt32)"))

LIN = """
let n := (rd32 st {nslot}).toNat
let lc := cx.linBase + cx.linUnit * n
if lc ≥ 2 ^ 62 then gasFail host acc lc pg gl else
let acc1 := acc + lc.toUInt64
if acc1 > lim then gasFail host acc lc pg gl else
"""
arm("memory_grow", LIN.format(nslot="i") + f"""
let old := pg.size
let newSize := old + n
if newSize > 65536 || cx.memMax.any (newSize > ·) then {k(st="(wr32 st i 0xFFFFFFFF)", acc="acc1")} else
{k(st="(wr32 st i old.toUInt32)", pg="(pg ++ Array.replicate n ByteArray.empty)", acc="acc1")}""")
arm("memory_fill", LIN.format(nslot="(i + 4)") + f"""
let d := (rd32 st i).toNat
if d + n > pg.size * 65536 then {trap(".outOfBoundsMemoryAccess", "acc1")} else
{k(pg="(NearFastVM.fill pg d n (rd32 st (i + 2)).toUInt8)", acc="acc1")}""")
arm("memory_copy", LIN.format(nslot="(i + 4)") + f"""
let d := (rd32 st i).toNat
let s := (rd32 st (i + 2)).toNat
if d + n > pg.size * 65536 || s + n > pg.size * 65536 then {trap(".outOfBoundsMemoryAccess", "acc1")} else
{k(pg="(NearFastVM.copy pg d s n)", acc="acc1")}""")

arm("i32_wrap_i64", k())
arm("i64_extend_i32_u", k(st="(wr st i (rd32 st i).toUInt64)"))
arm("i64_extend_i32_s", k(st="(wr st i (rd32 st i).toInt32.toInt64.toUInt64)"))
arm("i32_eqz", k(st="(wr32 st i (b2u32 (rd32 st i == 0)))"))
arm("i64_eqz", k(st="(wr32 st i (b2u32 (rd st i == 0)))"))
arm("cold", f"""
match execCold fc.colds[ins.imm.toNat]! st i with
| .ok v => {k(st="(wr st i v)")}
| .error t => finish host acc pg gl (.trap t)""")

OPEXPR32 = {
    "add": "a + b", "sub": "a - b", "mul": "a * b", "and": "a &&& b", "or": "a ||| b", "xor": "a ^^^ b",
    "shl": "a <<< (b % 32)", "shr_u": "a >>> (b % 32)", "shr_s": "shrs32 a b", "rotl": "rotl32 a b",
    "rotr": "rotr32 a b",
}
OPEXPR64 = {
    "add": "a + b", "sub": "a - b", "mul": "a * b", "and": "a &&& b", "or": "a ||| b", "xor": "a ^^^ b",
    "shl": "a <<< (b % 64)", "shr_u": "a >>> (b % 64)", "shr_s": "shrs64 a b", "rotl": "rotl64 a b",
    "rotr": "rotr64 a b",
}
REL32 = {"eq": "a == b", "ne": "a != b", "lt_u": "a < b", "gt_u": "a > b", "le_u": "a ≤ b", "ge_u": "a ≥ b",
         "lt_s": "a.toInt32 < b.toInt32", "gt_s": "a.toInt32 > b.toInt32", "le_s": "a.toInt32 ≤ b.toInt32",
         "ge_s": "a.toInt32 ≥ b.toInt32"}
REL64 = {"eq": "a == b", "ne": "a != b", "lt_u": "a < b", "gt_u": "a > b", "le_u": "a ≤ b", "ge_u": "a ≥ b",
         "lt_s": "a.toInt64 < b.toInt64", "gt_s": "a.toInt64 > b.toInt64", "le_s": "a.toInt64 ≤ b.toInt64",
         "ge_s": "a.toInt64 ≥ b.toInt64"}

for w, bits in (("i32", 32), ("i64", 64)):
    rdA = "rd32 st i" if w == "i32" else "rd st i"
    rdB = "rd32 st (i + 2)" if w == "i32" else "rd st (i + 2)"
    wrR = (lambda e: f"wr32 st i ({e})") if w == "i32" else (lambda e: f"wr st i ({e})")
    exprs = OPEXPR32 if w == "i32" else OPEXPR64
    rels = REL32 if w == "i32" else REL64
    minval = "0x80000000" if w == "i32" else "0x8000000000000000"
    minus1 = "0xFFFFFFFF" if w == "i32" else "0xFFFFFFFFFFFFFFFF"
    for o in I_BIN:
        pre = f"""
let a := {rdA}
let b := {rdB}
"""
        if o in exprs:
            arm(f"{w}_{o}", pre + k(st=f"({wrR(exprs[o])})"))
        elif o in ("div_u", "rem_u"):
            sym = "/" if o == "div_u" else "%"
            arm(f"{w}_{o}", pre + f"""
if b == 0 then {trap(".integerDivideByZero")} else
{k(st=f"({wrR(f'a {sym} b')})")}""")
        elif o == "div_s":
            arm(f"{w}_{o}", pre + f"""
if b == 0 then {trap(".integerDivideByZero")} else
if a == {minval} && b == {minus1} then {trap(".integerOverflow")} else
{k(st=f"({wrR(f'divs{bits} a b')})")}""")
        elif o == "rem_s":
            arm(f"{w}_{o}", pre + f"""
if b == 0 then {trap(".integerDivideByZero")} else
{k(st=f"({wrR(f'rems{bits} a b')})")}""")
    for o in I_REL:
        arm(f"{w}_{o}", f"""
let a := {rdA}
let b := {rdB}
""" + k(st=f"(wr32 st i (b2u32 ({rels[o]})))"))
    un = {"clz": f"clz{bits} a", "ctz": f"ctz{bits} a", "popcnt": f"popcnt{bits} a"}
    if w == "i32":
        un["extend8_s"] = "a.toUInt8.toInt8.toInt32.toUInt32"
        un["extend16_s"] = "a.toUInt16.toInt16.toInt32.toUInt32"
    else:
        un["extend8_s"] = "a.toUInt8.toInt8.toInt64.toUInt64"
        un["extend16_s"] = "a.toUInt16.toInt16.toInt64.toUInt64"
    for o in (I_UN32 if w == "i32" else I_UN64):
        arm(f"{w}_{o}", f"""
let a := {rdA}
""" + k(st=f"({wrR(un[o])})"))

header = '''import NearFastVM.Compile
import NearFastVM.ExecCore

/-! Generated by `scripts/gen_exec.py`; do not edit. -/

/-!
# The interpreter loop

One iteration: fetch the instruction, charge its gas (`acc` is what has been spent since the host state was last
synchronised, `lim` how much may be spent before a limit is hit), run it. The loop calls only itself, in tail
position, so it compiles to a C loop; everything that can fail returns a `Final`.
-/

namespace NearFastVM

open Wasm Wasm.Near

partial def loop (cx : Ctx) (fns : Array (Option FnCode)) (fc : FnCode) (fid : Nat) (pc fp : USize)
    (st gl : Array UInt32) (pg : Array ByteArray) (fr : Array UInt32) (depth : USize) (host : NearState)
    (acc lim : UInt64) : Final :=
  let ins := fc.code[pc.toNat]!
  let acc0 := acc
  let acc := acc + ins.cost
  if acc > lim then gasFail host acc0 ins.cost.toNat pg gl else
  let i := fp + ins.x.toUSize
  match ins.op with
'''
footer = '''
end NearFastVM
'''
out = header + "\n".join(arms) + footer
pathlib.Path(__file__).resolve().parent.parent.joinpath("NearFastVM/Exec.lean").write_text(out)
