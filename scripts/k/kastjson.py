"""kastjson — parse `krun --output json` (KAST v3) final configurations of the
traced MPY build into Python events and Python-rendered values.

Label names in KAST JSON are fully qualified (e.g.
`lineEvt(_,_,_)_MPY-TRACE_TraceEvt_Int_Map_Map`); we match on the base name
before the first parenthesis/underscore-qualifier.
"""
from __future__ import annotations

import json
from typing import Any


def base(label: str) -> str:
    """`lineEvt(_,_,_)_MPY-TRACE_...` -> `lineEvt`; `<trace>` -> `<trace>`."""
    for i, ch in enumerate(label):
        if ch in "(_" and i > 0:
            return label[:i]
    return label


def lbl(node: dict) -> str:
    return base(node["label"]["name"]) if node["node"] == "KApply" else ""


def cells(term: dict) -> dict[str, dict]:
    """Flatten the configuration into {cell-name: content-node}."""
    out: dict[str, dict] = {}

    def walk(n: dict) -> None:
        if n["node"] == "KApply":
            name = n["label"]["name"]
            if name.startswith("<") and name.endswith(">"):
                if len(n["args"]) == 1 and not (
                    n["args"][0]["node"] == "KApply"
                    and n["args"][0]["label"]["name"].startswith("<")
                ):
                    out[name] = n["args"][0]
            for a in n["args"]:
                walk(a)

    walk(term)
    return out


def flat_assoc(node: dict, cons_bases: tuple[str, ...], unit_bases: tuple[str, ...]) -> list[dict]:
    """Flatten an assoc/cons structure (List, Map, Vals, ValSeq...) into leaves."""
    items: list[dict] = []

    def walk(n: dict) -> None:
        if n["node"] == "KApply":
            b = lbl(n)
            if b in unit_bases:
                return
            if b in cons_bases:
                for a in n["args"]:
                    walk(a)
                return
        items.append(n)

    walk(node)
    return items


def klist_items(node: dict) -> list[dict]:
    """K List cell -> the terms inside ListItem(_)."""
    leaves = flat_assoc(node, ("_List",), (".List",))
    out = []
    for leaf in leaves:
        assert lbl(leaf) == "ListItem", f"unexpected List leaf {lbl(leaf)}"
        out.append(leaf["args"][0])
    return out


def kmap_entries(node: dict) -> list[tuple[dict, dict]]:
    leaves = flat_assoc(node, ("_Map",), (".Map",))
    out = []
    for leaf in leaves:
        assert lbl(leaf) == "_|->", f"unexpected Map leaf {lbl(leaf)}"
        out.append((leaf["args"][0], leaf["args"][1]))
    return out


def kvals(node: dict) -> list[dict]:
    """MPY `Vals` (List{Val,","}) -> leaf list. Unit labels vary in spelling
    (`.Vals`, `.List{"_,_"}`), so anything starting with `.` is a unit."""
    items: list[dict] = []

    def walk(n: dict) -> None:
        if n["node"] == "KApply":
            b = lbl(n)
            if b.startswith("."):
                return
            if b == "_," and len(n["args"]) == 2:
                for a in n["args"]:
                    walk(a)
                return
        items.append(n)

    walk(node)
    return items


def token(node: dict) -> Any:
    assert node["node"] == "KToken", node
    sort, tok = node["sort"]["name"], node["token"]
    if sort == "Int":
        return int(tok)
    if sort == "Bool":
        return tok == "true"
    if sort == "String":
        return json.loads(tok)
    return tok


def _intseq_codes(node: dict) -> list[int]:
    codes = []
    while lbl(node) == "iCons":
        codes.append(token(node["args"][0]))
        node = node["args"][1]
    return codes


def _valseq(node: dict) -> list[dict]:
    vals = []
    while lbl(node) == "vCons":
        vals.append(node["args"][0])
        node = node["args"][1]
    return vals


class Renderer:
    """Render MPY `Val` terms as Python values, deref'ing heap refs against the
    heap snapshot captured in the same trace event."""

    def __init__(self, heap_node: dict | None):
        self.heap: dict[int, dict] = {}
        if heap_node is not None:
            for k, v in kmap_entries(heap_node):
                self.heap[token(k)] = v

    def val(self, n: dict, name_hint: str | None = None) -> Any:
        if n["node"] == "KToken":
            return token(n)
        b = lbl(n)
        if b == "noneV":
            return None
        if b == "str":
            return "".join(chr(c) for c in _intseq_codes(n["args"][0]))
        if b == "list":
            return [self.val(v) for v in _valseq(n["args"][0])]
        if b == "tuple":
            return tuple(self.val(v) for v in _valseq(n["args"][0]))
        if b == "ref":
            return self.val(self.heap[token(n["args"][0])])
        if b == "cellV":
            return self.val(n["args"][0])
        if b == "cellRef":
            return self.val(self.heap[token(n["args"][0])])
        if b in ("closureVal", "closureValC"):
            return f"<function {name_hint}>" if name_hint else "<function>"
        if b in ("builtinV", "typeV"):
            return f"<builtin {token(n['args'][0])}>"
        if b == "rangeObj":
            a, z, s = (self.val(x) for x in n["args"])
            return f"range({a}, {z}, {s})"
        raise ValueError(f"unrenderable Val: {b}")

    def scope_locals(self, map_node: dict) -> dict[str, Any]:
        out = {}
        for k, v in kmap_entries(map_node):
            name = token(k)
            if name == "$cells":
                continue
            out[name] = self.val(v, name_hint=name)
        return out


def raw_events(term: dict) -> list[tuple]:
    """<trace> cell -> [('line', line, locals), ('call', [args]), ('return', value, locals)]."""
    cs = cells(term)
    evts: list[tuple] = []
    for item in klist_items(cs["<trace>"]):
        b = lbl(item)
        if b == "lineEvt":
            line_n, scope_n, heap_n = item["args"]
            r = Renderer(heap_n)
            evts.append(("line", token(line_n), r.scope_locals(scope_n)))
        elif b == "callEvt":
            r = Renderer(None)
            evts.append(("call", [r.val(v) for v in kvals(item["args"][0])]))
        elif b == "retEvt":
            val_n, scope_n, heap_n = item["args"]
            r = Renderer(heap_n)
            evts.append(("return", r.val(val_n), r.scope_locals(scope_n)))
        else:
            raise ValueError(f"unknown trace event {b}")
    return evts


def exc_name(term: dict) -> str | None:
    node = cells(term)["<exc>"]
    b = lbl(node) or token(node)
    return None if b == "NoExc" else b


def module_result(term: dict) -> Any:
    """The value bound to `result` in the module scope (loc 0), if any."""
    cs = cells(term)
    for k, v in kmap_entries(cs["<scopes>"]):
        if token(k) == 0:
            assert lbl(v) == "scope"
            r = Renderer(cs.get("<heap>"))
            m = r.scope_locals(v["args"][0])
            return m.get("result")
    return None
