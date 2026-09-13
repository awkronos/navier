#!/usr/bin/env python3
"""Checker for the navier formalization manifest (strict-subset YAML loader).

Modes:
  --check   validate structure, statuses, axiom allowlist, and name location.
  --probe   print `lake env lean` + #print axioms commands for THEOREM rows
            (commands only; never executes, never fabricates results).

Name-location is a regex aid only: THEOREM rows must match `theorem <name>`;
other statuses match any declaration keyword (def/theorem/lemma/...). It says
nothing about proof status.
"""
import argparse
import re
import sys
from pathlib import Path

STATUS_TOKENS = {"THEOREM", "CONDITIONAL_THEOREM", "OPEN", "FALSIFIED"}
AXIOM_ALLOWLIST = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_KEYS = ("id", "declaration", "file", "status", "evidence", "statement")


def _unquote(v):
    v = v.strip()
    if len(v) >= 2 and v[0] == '"' and v[-1] == '"':
        return v[1:-1]
    return v


def _parse_inline_list(v):
    inner = v.strip()[1:-1]
    return [_unquote(p) for p in inner.split(",") if p.strip()]


def load_yaml_subset(path):
    """Parse: top-level `key: value`, `rows:` list of flat mappings, and
    one-line inline lists. Quoted scalars only; no nesting, no block lists."""
    top, rows, cur = {}, [], None
    in_rows = False
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.rstrip()
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if line.startswith("rows:"):
            in_rows = True
            continue
        if in_rows and (line.startswith("  - ") or line.startswith("    ")) :
            body = line.strip()
            if body.startswith("- "):
                cur = {}
                rows.append(cur)
                body = body[2:]
            key, _, val = body.partition(":")
            key, val = key.strip(), val.strip()
            if cur is None:
                raise ValueError(f"row key outside a row: {body}")
            if key == "axioms":
                cur[key] = _parse_inline_list(val)
            else:
                cur[key] = _unquote(val)
            continue
        in_rows = False
        key, _, val = line.partition(":")
        top[key.strip()] = _unquote(val)
    top["rows"] = rows
    return top


def check(manifest_path, root):
    errors = []
    try:
        doc = load_yaml_subset(manifest_path)
    except Exception as exc:  # fail closed on any parse problem
        print(f"PARSE ERROR: {exc}")
        return 1
    rows = doc.get("rows") or []
    if not rows:
        errors.append("manifest has no rows")
    for i, row in enumerate(rows):
        rid = row.get("id", f"<row {i}>")
        for key in REQUIRED_KEYS:
            if key not in row or not str(row[key]).strip():
                errors.append(f"{rid}: missing/empty required key `{key}`")
        status = row.get("status", "")
        if status not in STATUS_TOKENS:
            errors.append(f"{rid}: unknown status token {status!r}")
            continue
        decl = row.get("declaration", "")
        name = decl.rsplit(".", 1)[-1]
        fpath = root / row.get("file", "")
        if not fpath.is_file():
            errors.append(f"{rid}: file not found: {row.get('file')}")
        elif not re.search(rf"^\s*(theorem|lemma|def|abbreviation|structure)\s+{re.escape(name)}\b",
                           fpath.read_text(encoding="utf-8"), re.M):
            errors.append(f"{rid}: declaration name `{name}` not found in {row.get('file')}")
        axioms = row.get("axioms")
        if status == "THEOREM":
            if axioms is None:
                errors.append(f"{rid}: THEOREM row lacks axioms field")
            else:
                for ax in axioms:
                    if ax not in AXIOM_ALLOWLIST:
                        errors.append(f"{rid}: axiom escapes allowlist: {ax!r}")
        elif axioms is not None:
            errors.append(f"{rid}: non-THEOREM row must not carry an axioms field")
    for err in errors:
        print(f"FAIL: {err}")
    if errors:
        return 1
    print(f"OK: {len(rows)} rows validated against {root}")
    return 0


def probe(manifest_path, root):
    doc = load_yaml_subset(manifest_path)
    for row in doc.get("rows") or []:
        if row.get("status") != "THEOREM":
            continue
        module = row["file"].removesuffix(".lean").replace("/", ".")
        scratch = f"/tmp/probe_{row['id']}.lean"
        print(f"# {row['id']}: run from {root}, then inspect stdout:")
        print(f"cd {root} && printf 'import {module}\\n#print axioms {row['declaration']}\\n'"
              f" > {scratch} && lake env lean {scratch}")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--probe", action="store_true")
    ap.add_argument("--manifest", required=True, type=Path)
    ap.add_argument("--root", required=True, type=Path)
    args = ap.parse_args()
    if args.check and args.probe:
        ap.error("--check and --probe are exclusive")
    if args.check:
        sys.exit(check(args.manifest, args.root))
    if args.probe:
        sys.exit(probe(args.manifest, args.root))
    ap.error("choose --check or --probe")


if __name__ == "__main__":
    main()
