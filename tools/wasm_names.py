#!/usr/bin/env python3
"""Name the functions of a stripped binary from a rebuild that kept its names.

usage: tools/wasm_names.py DEPLOYED.wasm NAMED.wasm OUT.tsv

The rebuild must differ from the deployed binary only in custom sections:
every other section is compared byte for byte, and the script fails if one
differs. The function names come from the rebuild's `name` section.

OUT.tsv has one row per function: its index, whether it is imported, the
byte size of its code entry, the exported methods that can reach it, and its
demangled Rust name. Reachability follows `call`, and `call_indirect` to the
table entries whose type is the one the instruction names. It needs the
pinned `wasm-tools` (see .github/workflows/wasm.yml).
"""

import re
import subprocess
import sys


def uleb(b, p):
    r = s = 0
    while True:
        x = b[p]
        p += 1
        r |= (x & 0x7F) << s
        s += 7
        if x < 0x80:
            return r, p


def sections(b):
    """(id, payload) for every section, custom sections with their name."""
    out = []
    p = 8
    while p < len(b):
        sid = b[p]
        size, q = uleb(b, p + 1)
        payload = b[q:q + size]
        if sid == 0:
            n, r = uleb(payload, 0)
            out.append((0, payload[r:r + n].decode(), payload[r + n:]))
        else:
            out.append((sid, None, payload))
        p = q + size
    return out


def function_names(payload):
    """The function-names subsection (id 1) of a `name` section."""
    p = 0
    names = {}
    while p < len(payload):
        sub = payload[p]
        size, q = uleb(payload, p + 1)
        if sub == 1:
            count, r = uleb(payload, q)
            for _ in range(count):
                idx, r = uleb(payload, r)
                n, r = uleb(payload, r)
                names[idx] = payload[r:r + n].decode()
                r += n
        p = q + size
    return names


ESCAPES = {"$LT$": "<", "$GT$": ">", "$RF$": "&", "$BP$": "*", "$C$": ",", "$SP$": "@",
           "$u20$": " ", "$u27$": "'", "$u5b$": "[", "$u5d$": "]", "$u7b$": "{", "$u7d$": "}",
           "$u7e$": "~", "$u3b$": ";", "$u2b$": "+", "$u22$": '"', "..": "::"}


def demangle(sym):
    """Rust's legacy mangling (`_ZN...E`), without the trailing hash."""
    if not sym.startswith("_ZN") or not sym.endswith("E"):
        return sym
    p, parts, body = 3, [], sym[:-1]
    while p < len(body):
        m = re.match(r"\d+", body[p:])
        if not m:
            return sym
        n = int(m.group())
        p += len(m.group())
        parts.append(body[p:p + n])
        p += n
    if parts and re.fullmatch(r"h[0-9a-f]{16}", parts[-1]):
        parts = parts[:-1]
    out = []
    for part in parts:
        if part.startswith("_$"):
            part = part[1:]
        for k, v in ESCAPES.items():
            part = part.replace(k, v)
        out.append(part)
    return "::".join(out)


def code_sizes(payload):
    n, p = uleb(payload, 0)
    sizes = []
    for _ in range(n):
        s, q = uleb(payload, p)
        sizes.append(q + s - p)
        p = q + s
    return sizes


def call_graph(path):
    """Calls of each function, the type of each function, the table, the exports."""
    wat = subprocess.run(["wasm-tools", "print", path], check=True, capture_output=True,
                         text=True).stdout
    types, calls, indirect, exports, table = {}, {}, {}, {}, []
    cur = None
    for line in wat.split("\n"):
        m = re.match(r"\s*\(import \"[^\"]*\" \"[^\"]*\" \(func \(;(\d+);\) \(type (\d+)\)", line)
        if m:
            types[int(m.group(1))] = int(m.group(2))
            continue
        m = re.match(r"\s*\(func (?:\$\S+ )?\(;(\d+);\) \(type (\d+)\)", line)
        if m:
            cur = int(m.group(1))
            types[cur] = int(m.group(2))
            calls[cur], indirect[cur] = set(), set()
            continue
        m = re.match(r"\s*\(export \"([^\"]*)\" \(func (\d+)\)\)", line)
        if m:
            exports[m.group(1)] = int(m.group(2))
            continue
        if line.strip().startswith("(elem"):
            table += [int(x) for x in re.findall(r"\b(\d+)\b", line.split(" func ", 1)[1])]
            continue
        if cur is not None:
            m = re.search(r"\bcall (\d+)\b", line)
            if m:
                calls[cur].add(int(m.group(1)))
            m = re.search(r"\bcall_indirect \(type (\d+)\)", line)
            if m:
                indirect[cur].add(int(m.group(1)))
    return types, calls, indirect, exports, table


def main():
    deployed_path, named_path, out_path = sys.argv[1:4]
    deployed = open(deployed_path, "rb").read()
    named = open(named_path, "rb").read()
    a = [(i, p) for i, _, p in sections(deployed) if i != 0]
    b = [(i, p) for i, _, p in sections(named) if i != 0]
    if a != b:
        diff = [i for (i, p), (_, q) in zip(a, b) if p != q] if len(a) == len(b) else "count"
        sys.exit(f"the rebuild differs from the deployed binary outside custom sections: {diff}")
    name_payload = next((p for i, n, p in sections(named) if i == 0 and n == "name"), None)
    if name_payload is None:
        sys.exit("the rebuild has no name section")
    names = function_names(name_payload)
    types, calls, indirect, exports, table = call_graph(deployed_path)
    imported = sum(1 for idx in types if idx not in calls)
    sizes = code_sizes(next(p for i, p in a if i == 10))
    reached = {idx: [] for idx in types}
    for method, root in sorted(exports.items()):
        seen, todo = set(), [root]
        while todo:
            f = todo.pop()
            if f in seen:
                continue
            seen.add(f)
            todo += calls.get(f, ())
            for t in indirect.get(f, ()):
                todo += [g for g in table if types[g] == t]
        for f in seen:
            reached[f].append(method)
    with open(out_path, "w") as out:
        out.write("# Generated by tools/wasm_names.py from contract.wasm and a rebuild that kept its "
                  "names; do not edit.\n")
        out.write("index\timported\tbytes\treached_by\tname\n")
        for idx in sorted(types):
            size = "" if idx < imported else str(sizes[idx - imported])
            out.write(f"{idx}\t{'yes' if idx < imported else 'no'}\t{size}\t"
                      f"{','.join(sorted(reached[idx])) or '-'}\t{demangle(names.get(idx, ''))}\n")
    print(f"{out_path}: {len(types)} functions, {imported} imported; non-custom sections identical")


if __name__ == "__main__":
    main()
