#!/usr/bin/env python3
"""Tiny TOML reader/writer for contract.toml files (stdlib only, Python 3.9+).

Supports the subset we emit: nested tables, arrays of tables, strings, ints,
bools and arrays of scalars. Values are serialised as JSON literals, which are
valid TOML for these types, so reading uses json.loads per value.
"""
import json, re

_KEY = re.compile(r"^[A-Za-z0-9_-]+$")


def _key(k):
    return k if _KEY.match(k) else json.dumps(k)


def _scalar(v):
    if isinstance(v, bool) or isinstance(v, (int, float)) or isinstance(v, str):
        return json.dumps(v, ensure_ascii=False)
    if isinstance(v, list) and all(not isinstance(x, (dict, list)) for x in v):
        return json.dumps([x for x in v if x is not None], ensure_ascii=False)
    raise TypeError(f"unsupported value {v!r}")


def dumps(d, prefix=()):
    out = []
    tables, arrays = [], []
    for k, v in d.items():
        if v is None:
            continue
        if isinstance(v, dict):
            tables.append((k, v))
        elif isinstance(v, list) and v and all(isinstance(x, dict) for x in v):
            arrays.append((k, v))
        else:
            out.append(f"{_key(k)} = {_scalar(v)}")
    text = "\n".join(out)
    for k, v in tables:
        sub = dumps(v, prefix + (k,))
        text += f"\n\n[{'.'.join(_key(p) for p in prefix + (k,))}]\n{sub}"
    for k, v in arrays:
        for item in v:
            sub = dumps(item, prefix + (k,))
            text += f"\n\n[[{'.'.join(_key(p) for p in prefix + (k,))}]]\n{sub}"
    return text.strip("\n") + ("\n" if not prefix else "")


def loads(text):
    root, cur = {}, None
    cur = root
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("[["):
            path = [_unquote(p) for p in _split_path(line[2:-2])]
            parent = root
            for p in path[:-1]:
                parent = parent.setdefault(p, {}) if not isinstance(parent.get(p), list) else parent[p][-1]
            cur = {}
            parent.setdefault(path[-1], []).append(cur)
        elif line.startswith("["):
            path = [_unquote(p) for p in _split_path(line[1:-1])]
            parent = root
            for p in path[:-1]:
                parent = parent.setdefault(p, {}) if not isinstance(parent.get(p), list) else parent[p][-1]
            cur = parent.setdefault(path[-1], {})
        else:
            k, _, v = line.partition("=")
            cur[_unquote(k.strip())] = json.loads(v.strip())
    return root


def _split_path(s):
    return [p.strip() for p in re.findall(r'"[^"]*"|[^.]+', s)]


def _unquote(s):
    return json.loads(s) if s.startswith('"') else s


def load(path):
    return loads(open(path, encoding="utf-8").read())


def dump(d, path):
    open(path, "w", encoding="utf-8").write(dumps(d))


if __name__ == "__main__":
    import sys
    d = json.load(open(sys.argv[1]))
    t = dumps(d)
    assert loads(t) == json.loads(json.dumps({k: v for k, v in d.items()}), object_hook=lambda o: {k: v for k, v in o.items() if v is not None}), "roundtrip mismatch"
    print(t)
