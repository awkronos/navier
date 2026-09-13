#!/usr/bin/env python3
"""Lean import-graph analyzer.

Scans .lean modules under one or more source directories rooted at --root,
parses `^import` lines, resolves module names to files, and reports:
cycles, longest-chain depth, fan-in hubs, roots (zero importers), and a
crown-relative classification of every module (consumed / root-research /
intermediate-unconsumed). Stdlib only.

Exit status: 0 clean, 1 import cycle(s) detected, 2 usage/IO error.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict, deque

IMPORT_RE = re.compile(r"^import\s+(.+)$")
MOD_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")


def scan_modules(root: str, dirs: list[str]) -> dict[str, str]:
    """Map module name -> file path for every .lean file under root/d for d in
    dirs, plus repo-root *.lean files (module name = filename sans .lean)."""
    import os
    mods: dict[str, str] = {}
    for fn in sorted(os.listdir(root)):
        if fn.endswith(".lean"):
            mods[fn[: -len(".lean")]] = os.path.join(root, fn)
    for d in dirs:
        base = os.path.join(root, d)
        if not os.path.isdir(base):
            print(f"warning: source dir missing: {base}", file=sys.stderr)
            continue
        for dirpath, _dirnames, filenames in os.walk(base):
            for fn in filenames:
                if not fn.endswith(".lean"):
                    continue
                path = os.path.join(dirpath, fn)
                rel = os.path.relpath(path, root)[: -len(".lean")]
                parts = rel.split(os.sep)
                if parts[-1] == "Default":
                    parts = parts[:-1]  # Lean 4: Foo/Bar/Default.lean is module Foo.Bar
                mods[".".join(parts)] = path
    return mods


def parse_imports(path: str) -> list[str]:
    out: list[str] = []
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            for line in fh:
                m = IMPORT_RE.match(line.strip())
                if not m:
                    continue
                body = m.group(1).split("--", 1)[0]
                for tok in re.split(r"[,\s]+", body):
                    if MOD_RE.match(tok):
                        out.append(tok)
    except OSError:
        pass
    return out


def build_graph(mods: dict[str, str]):
    edges: set[tuple[str, str]] = set()
    fwd: dict[str, list[str]] = defaultdict(list)   # module -> imported modules
    rev: dict[str, list[str]] = defaultdict(list)   # module -> importers
    unresolved = 0
    for name, path in mods.items():
        for target in parse_imports(path):
            if target == name:
                continue
            if target in mods:
                if (name, target) not in edges:
                    edges.add((name, target))
                    fwd[name].append(target)
                    rev[target].append(name)
            else:
                unresolved += 1
    return edges, fwd, rev, unresolved


def find_cycles(nodes, fwd):
    """Iterative DFS; returns up to 5 distinct cycles (each a list of module names)."""
    WHITE, GRAY, BLACK = 0, 1, 2
    color = {n: WHITE for n in nodes}
    parent: dict[str, str | None] = {}
    cycles: list[list[str]] = []
    for start in nodes:
        if color[start] != WHITE or len(cycles) >= 5:
            continue
        stack = [(start, iter(fwd.get(start, ())))]
        color[start] = GRAY
        parent[start] = None
        while stack and len(cycles) < 5:
            node, it = stack[-1]
            advanced = False
            for nxt in it:
                if color[nxt] == WHITE:
                    color[nxt] = GRAY
                    parent[nxt] = node
                    stack.append((nxt, iter(fwd.get(nxt, ()))))
                    advanced = True
                    break
                if color[nxt] == GRAY:  # back edge -> cycle
                    chain = [node]
                    while chain[-1] != nxt and parent[chain[-1]] is not None:
                        chain.append(parent[chain[-1]])
                    cycles.append(list(reversed(chain)))
            if not advanced:
                color[node] = BLACK
                stack.pop()
    return cycles


def longest_depth(nodes, fwd):
    """Longest import-chain length (edges) over the condensation, so cyclic
    input still yields a finite number."""
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on_stack: set[str] = set()
    comp_of: dict[str, int] = {}
    comps: list[list[str]] = []

    def strongconnect(root_node):
        work = [(root_node, iter(fwd.get(root_node, ())))]
        while work:
            v, it = work[-1]
            if v not in index:
                index[v] = low[v] = len(index)
                stack.append(v)
                on_stack.add(v)
            resumed = False
            for w in it:
                if w not in index:
                    work.append((w, iter(fwd.get(w, ()))))
                    resumed = True
                    break
                if w in on_stack:
                    low[v] = min(low[v], index[w])
            if resumed:
                continue
            work.pop()
            if work:
                p = work[-1][0]
                low[p] = min(low[p], low[v])
            if low[v] == index[v]:
                cid = len(comps)
                members = []
                while True:
                    w = stack.pop()
                    on_stack.discard(w)
                    comp_of[w] = cid
                    members.append(w)
                    if w == v:
                        break
                comps.append(members)

    for n in nodes:
        if n not in index:
            strongconnect(n)

    cfwd = [set() for _ in comps]
    for s in nodes:
        for d in fwd.get(s, ()):
            a, b = comp_of[s], comp_of[d]
            if a != b:
                cfwd[a].add(b)
    # DAG longest path via topological order (Kahn) on condensation.
    indeg = [0] * len(comps)
    for a, nbrs in enumerate(cfwd):
        for b in nbrs:
            indeg[b] += 1
    order: list[int] = []
    dq = deque(i for i, d in enumerate(indeg) if d == 0)
    deg = indeg[:]
    while dq:
        c = dq.popleft()
        order.append(c)
        for b in cfwd[c]:
            deg[b] -= 1
            if deg[b] == 0:
                dq.append(b)
    dist = [0] * len(comps)
    for c in order:
        for b in cfwd[c]:
            if dist[b] < dist[c] + 1:
                dist[b] = dist[c] + 1
    intra = [len(cs) - 1 for cs in comps]
    return max((dist[c] + intra[c] for c in range(len(comps))), default=0)


def closure(crowns, fwd):
    """Modules transitively imported by any crown (including the crowns)."""
    seen = set(c for c in crowns if c in _known)
    dq = deque(seen)
    while dq:
        for nxt in fwd.get(dq.popleft(), ()):
            if nxt not in seen:
                seen.add(nxt)
                dq.append(nxt)
    return seen


def main(argv=None) -> int:
    global _known
    ap = argparse.ArgumentParser(description="Lean import-graph analyzer")
    ap.add_argument("--root", required=True, help="repository root to scan")
    ap.add_argument("--dirs", nargs="+", required=True,
                    help="source directories under root containing modules")
    ap.add_argument("--crown", action="append", default=[],
                    help="crown module name (repeatable)")
    ap.add_argument("--json", dest="json_out", help="write full stats as JSON")
    ap.add_argument("--top", type=int, default=10, help="hub table size")
    ap.add_argument("--partition", nargs=2, metavar=("A", "B"),
                    help="cross-import count between top-level module prefixes A and B")
    ap.add_argument("--umbrella", action="append", default=[],
                    help="umbrella module NAME: report coverage holes = scanned "
                         "modules not in its transitive import closure")
    args = ap.parse_args(argv)

    mods = scan_modules(args.root, args.dirs)
    if not mods:
        print("no .lean modules found", file=sys.stderr)
        return 2
    _known = set(mods)
    edges, fwd, rev, unresolved = build_graph(mods)

    cycles = find_cycles(mods.keys(), fwd)
    depth = longest_depth(mods.keys(), fwd)
    fan_in = {m: len(rev.get(m, ())) for m in mods}
    roots = sorted(m for m, f in fan_in.items() if f == 0)
    hubs = sorted(mods, key=lambda m: (-fan_in[m], m))[: args.top]

    for c in args.crown:
        if c not in mods:
            print(f"warning: crown not found in scan set: {c}", file=sys.stderr)
    consumed = closure(args.crown, fwd) if args.crown else set()
    root_research = [m for m in roots if m not in consumed]
    intermediate = sorted(m for m in mods if fan_in[m] > 0 and m not in consumed)

    umbrellas: dict[str, dict] = {}
    for u in args.umbrella:
        if u not in mods:
            print(f"warning: umbrella not found in scan set: {u}", file=sys.stderr)
            continue
        uclosure = closure([u], fwd)
        holes = sorted(set(mods) - uclosure)
        umbrellas[u] = {
            "closure_size": len(uclosure),
            "coverage_holes": len(holes),
            "coverage_hole_modules": holes,
            "crowns_in_closure": {c: c in uclosure for c in args.crown},
        }

    dir_rollup: dict[str, dict[str, int]] = defaultdict(
        lambda: {"modules": 0, "loc": 0})
    total_loc = 0
    for name, path in mods.items():
        try:
            loc = sum(1 for _ in open(path, "r", encoding="utf-8", errors="replace"))
        except OSError:
            loc = 0
        total_loc += loc
        key = "/".join(name.split(".")[:2]) if "." in name else name
        dir_rollup[key]["modules"] += 1
        dir_rollup[key]["loc"] += loc

    part = None
    if args.partition:
        a, b = args.partition
        ab = sum(1 for s, d in edges
                 if s.split(".")[0] == a and d.split(".")[0] == b)
        ba = sum(1 for s, d in edges
                 if s.split(".")[0] == b and d.split(".")[0] == a)
        part = {"prefixes": [a, b], f"{a}->{b}": ab, f"{b}->{a}": ba, "total": ab + ba}

    stats = {
        "root": args.root, "dirs": args.dirs,
        "modules": len(mods), "edges": len(edges),
        "unresolved_import_edges": unresolved,
        "total_loc": total_loc, "max_depth_edges": depth,
        "cycles_found": len(cycles), "cycles": cycles,
        "roots_count": len(roots), "roots": roots,
        "hubs": [{"module": m, "fan_in": fan_in[m]} for m in hubs],
        "crowns": args.crown,
        "closure_size": {c: len(closure([c], fwd)) for c in args.crown},
        "classification": {
            "consumed": len(consumed),
            "root_research": len(root_research),
            "intermediate_unconsumed": len(intermediate),
        },
        "consumed_modules": sorted(consumed),
        "root_research_modules": root_research,
        "intermediate_unconsumed_modules": intermediate,
        "per_directory": {k: dir_rollup[k] for k in sorted(dir_rollup)},
    }
    if part:
        stats["partition"] = part
    if umbrellas:
        stats["umbrellas"] = umbrellas

    if args.json_out:
        with open(args.json_out, "w", encoding="utf-8") as fh:
            json.dump(stats, fh, indent=1)

    print(f"modules={len(mods)}  edges={len(edges)}  unresolved_imports={unresolved}")
    print(f"total_loc={total_loc}  max_depth_edges={depth}")
    print(f"cycles={len(cycles)}  roots(zero-importers)={len(roots)}")
    if cycles:
        for cyc in cycles[:5]:
            print("  cycle: " + " -> ".join(cyc + [cyc[0]]))
    if args.crown:
        print(f"crowns: {', '.join(args.crown)}")
        print(f"  consumed={len(consumed)}  root-research={len(root_research)}  "
              f"intermediate-unconsumed={len(intermediate)}")
        for c in args.crown:
            print(f"  closure[{c}] = {stats['closure_size'][c]}")
    for u, info in umbrellas.items():
        print(f"umbrella {u}: closure={info['closure_size']}  "
              f"coverage-holes={info['coverage_holes']}")
        for c, ok in info["crowns_in_closure"].items():
            print(f"  crown-in-umbrella-closure[{c}] = {ok}")
        for h in info["coverage_hole_modules"][:20]:
            print(f"    hole: {h}")
        if info["coverage_holes"] > 20:
            print(f"    ... {info['coverage_holes'] - 20} more (see --json)")
    print(f"top-{args.top} hubs (fan-in):")
    for m in hubs:
        print(f"  {fan_in[m]:6d}  {m}")
    if part:
        print(f"partition {part['prefixes'][0]}<->{part['prefixes'][1]} "
              f"cross-imports={part['total']}")
    if args.json_out:
        print(f"json written: {args.json_out}")
    return 1 if cycles else 0


if __name__ == "__main__":
    sys.exit(main())
