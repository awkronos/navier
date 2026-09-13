#!/usr/bin/env python3
"""check_construction_drift.py — vendored-slice drift guard for navier.

For every Lean file under Navier/Construction (navier repo), the checker:

  1. reads the file's leading license header and extracts the declared
     upstream source path ("Upstream source: NavierStokes/.../X.lean").
     Files whose header declares repository-native provenance (and no
     upstream path) are classified NATIVE and body-compared against nothing.
     Files with neither an upstream path nor a native declaration are
     UNMAPPED-HEADER.
  2. fetches the upstream blob at the pinned revision from a read-only
     clone: `git -C <clone> show <pin>:<upstreamPath>` (missing path at the
     pin -> UPSTREAM-MISSING).
  3. normalizes BOTH sides:
       - drop the leading `/- ... -/` license block (present only navier-side),
       - split off the leading `import` lines (rewriting the module prefix
         NavierStokes. <-> Navier.Construction. before comparing them as a set),
       - drop the leading `/-! ... -/` doc-comment block(s),
       - rewrite the declared namespace/path adaptations through the body:
           NavierStokesR3  -> Navier.ConstructionR3
           NavierStokes/   -> Navier/Construction/   (comment path refs)
           NavierStokes.   -> Navier.Construction.
         (applied to both sides; idempotent on already-rewritten text),
       - strip trailing whitespace and drop blank lines (cosmetic-only).
  4. compares the remaining body text.

Statuses: IDENTICAL (modulo the declared adaptations) / DRIFT (unified-diff
line count + first 3 hunk headers) / UPSTREAM-MISSING / UNMAPPED-HEADER /
NATIVE.  Exit code 0 iff no DRIFT rows.

This proves the vendored slice still matches the PIN (8937a8f). Upstream
movement (e.g. f9e8bc5 +188 appendix files) is intentionally NOT probed:
the appendix-port lane needs "slice == pin", not "new files exist".

Read-only: only `git show` / `git cat-file` against the clone; writes nothing
outside stdout. Stdlib only.
"""

from __future__ import annotations

import argparse
import difflib
import re
import subprocess
import sys
from pathlib import Path

DEFAULT_PIN = "8937a8f4cbc7abaab5e9e97d1cc7f5d2319d9538"
DEFAULT_NAVIER_CONSTRUCTION = "/tmp/navier-crown/Navier/Construction"
DEFAULT_UPSTREAM_CLONE = "/tmp/ns-audit"

UPSTREAM_SOURCE_RE = re.compile(r"^Upstream source:[ \t]*(\S.*?)\s*$", re.M)
NATIVE_MARKERS = (
    "Repository-native",
    "repository-native",
    "Not adapted from upstream",
    "Native to this repository",
)

# Declared adaptation rewrites (see license headers: "Changes: native module
# namespace; further compatibility edits are in Git history.").
PREFIX_REWRITES = (
    ("NavierStokesR3", "Navier.ConstructionR3"),
    ("NavierStokes/", "Navier/Construction/"),
    ("NavierStokes.", "Navier.Construction."),
    ("NavierStokesR3", "Navier.ConstructionR3"),  # idempotent safety
)


def run_git(clone: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", "-C", str(clone), *args],
        capture_output=True,
        text=True,
    )


def _find_block_end(lines: list[str], start: int):
    """Scan nested /- ... -/ block comment starting at lines[start].
    Return the index of the line containing the matching '-/', or None."""
    depth = 0
    i = start
    while i < len(lines):
        line = lines[i]
        k = 0
        while k < len(line):
            if line.startswith("/-", k):
                depth += 1
                k += 2
            elif line.startswith("-/", k) and depth > 0:
                depth -= 1
                k += 2
                if depth == 0:
                    return i
            else:
                k += 1
        i += 1
    return None


def strip_block_comment_prefix(text: str, opener: str) -> str:
    """If `text` (after optional blank lines) starts with a block comment of
    the given kind (opener '/-' = plain, excluding '/-!'; opener '/-!' = doc
    block), remove it. Repeats while further such blocks follow."""
    while True:
        lines = text.split("\n")
        i = 0
        while i < len(lines) and lines[i].strip() == "":
            i += 1
        if i >= len(lines):
            return text
        first = lines[i]
        if opener == "/-":
            matched = first.startswith("/-") and not first.startswith("/-!")
        else:
            matched = first.startswith("/-!")
        if not matched:
            return text
        end = _find_block_end(lines, i)
        if end is None:
            return text  # unbalanced; leave untouched
        text = "\n".join(lines[end + 1 :])


def split_imports(text: str):
    """Pull leading `import ...` lines (blank lines interleaved allowed) off
    the top. Returns (import_module_set, remaining_text)."""
    lines = text.split("\n")
    imports = []
    i = 0
    last_import = -1
    while i < len(lines):
        s = lines[i].strip()
        if s == "":
            i += 1
            continue
        if s.startswith("import ") or s == "import":
            mod = s[len("import ") :].strip() if len(s) > 7 else ""
            if mod:
                imports.append(mod)
            last_import = i
            i += 1
            continue
        break
    if last_import < 0:
        return set(), text
    return set(imports), "\n".join(lines[last_import + 1 :])


def rewrite_prefixes(text: str) -> str:
    for old, new in PREFIX_REWRITES:
        text = text.replace(old, new)
    return text


def normalize(text: str) -> tuple[set, list[str]]:
    """Return (import set, normalized body lines) for either side."""
    # 1. leading license block (navier only; no-op if absent)
    text = strip_block_comment_prefix(text, "/-")
    # 2. leading imports
    imports, text = split_imports(text)
    # 3. leading doc-comment blocks /-! ... -/
    text = strip_block_comment_prefix(text, "/-!")
    # 4. declared adaptation rewrites (body; and imports before comparing)
    text = rewrite_prefixes(text)
    imports = {rewrite_prefixes(m) for m in imports}
    # 5. strip trailing whitespace, drop blank lines
    body = [ln.rstrip() for ln in text.split("\n")]
    body = [ln for ln in body if ln.strip() != ""]
    return imports, body


def fetch_upstream(clone: Path, pin: str, upath: str, cache: dict):
    if upath in cache:
        return cache[upath]
    r = run_git(clone, "show", f"{pin}:{upath}")
    if r.returncode == 0:
        res = ("ok", r.stdout)
    elif "does not exist" in r.stderr or "not found" in r.stderr or "exists on disk" in r.stderr:
        res = ("missing", None)
    else:
        res = ("error", r.stderr.strip())
    cache[upath] = res
    return res


def diff_stats(navy: list[str], ups: list[str]):
    """(changed-line count, first 3 hunk headers) of a unified diff."""
    out = list(
        difflib.unified_diff(ups, navy, fromfile="upstream", tofile="navier", lineterm="")
    )
    changed = sum(
        1
        for ln in out
        if (ln.startswith("+") and not ln.startswith("+++"))
        or (ln.startswith("-") and not ln.startswith("---"))
    )
    hunks = [ln for ln in out if ln.startswith("@@")][:3]
    return changed, hunks


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--construction", default=DEFAULT_NAVIER_CONSTRUCTION)
    ap.add_argument("--clone", default=DEFAULT_UPSTREAM_CLONE)
    ap.add_argument("--pin", default=DEFAULT_PIN)
    ap.add_argument("--verbose", action="store_true", help="print IDENTICAL rows too")
    args = ap.parse_args(argv)

    construction = Path(args.construction)
    clone = Path(args.clone)
    pin = args.pin

    if not construction.is_dir():
        print(f"error: construction dir not found: {construction}", file=sys.stderr)
        return 2
    v = run_git(clone, "cat-file", "-e", pin)
    if v.returncode != 0:
        print(f"error: pin {pin} not present in clone {clone}", file=sys.stderr)
        return 2

    files = sorted(construction.rglob("*.lean"))
    counts = {k: 0 for k in ("IDENTICAL", "DRIFT", "UPSTREAM-MISSING", "UNMAPPED-HEADER", "NATIVE")}
    drift_rows: list[tuple[str, int, list[str], str]] = []
    unmapped_rows: list[str] = []
    missing_rows: list[str] = []
    native_rows: list[str] = []
    blob_cache: dict = {}

    for f in files:
        rel = str(f.relative_to(construction))
        text = f.read_text(encoding="utf-8")

        header_match = UPSTREAM_SOURCE_RE.search(text[:4000])
        header_block = text[:4000]
        is_native = any(m in header_block for m in NATIVE_MARKERS)

        if header_match is None:
            if is_native:
                counts["NATIVE"] += 1
                native_rows.append(rel)
                if args.verbose:
                    print(f"NATIVE          {rel}")
            else:
                counts["UNMAPPED-HEADER"] += 1
                unmapped_rows.append(rel)
                print(f"UNMAPPED-HEADER {rel}  (no 'Upstream source:' line and no native marker in header)")
            continue

        upath = header_match.group(1).strip()
        state, payload = fetch_upstream(clone, pin, upath, blob_cache)
        if state == "missing":
            counts["UPSTREAM-MISSING"] += 1
            missing_rows.append(rel)
            print(f"UPSTREAM-MISSING {rel}  -> {pin[:7]}:{upath}")
            continue
        if state == "error":
            counts["UNMAPPED-HEADER"] += 1
            unmapped_rows.append(rel)
            print(f"UNMAPPED-HEADER {rel}  (git show failed: {payload})")
            continue

        navy_imports, navy_body = normalize(text)
        ups_imports, ups_body = normalize(payload)
        imp_only = navy_body == ups_body
        if navy_imports == ups_imports and navy_body == ups_body:
            counts["IDENTICAL"] += 1
            if args.verbose:
                print(f"IDENTICAL       {rel}  <- {upath}")
            continue

        counts["DRIFT"] += 1
        changed, hunks = diff_stats(navy_body, ups_body)
        extra = " (imports differ only: body identical)" if imp_only else ""
        drift_rows.append((rel, changed, hunks, upath + extra))
        print(f"DRIFT           {rel}  <- {upath}  [{changed} changed lines]{extra}")
        for h in hunks:
            print(f"    hunk {h}")

    total = len(files)
    print()
    print("=" * 64)
    print("ROLLUP — navier Construction vs upstream PIN " + pin[:7])
    print(f"  files scanned      : {total}")
    print(f"  IDENTICAL          : {counts['IDENTICAL']}")
    print(f"  DRIFT              : {counts['DRIFT']}")
    print(f"  UPSTREAM-MISSING   : {counts['UPSTREAM-MISSING']}")
    print(f"  UNMAPPED-HEADER    : {counts['UNMAPPED-HEADER']}")
    print(f"  NATIVE             : {counts['NATIVE']}")
    ok = counts["DRIFT"] == 0
    print(f"  VERDICT            : {'NO DRIFT vs pin' if ok else 'DRIFT PRESENT'}")
    print("=" * 64)
    if drift_rows:
        print("drifted files:")
        for rel, changed, hunks, upath in drift_rows:
            print(f"  {rel} ({changed} lines vs {upath})")
    if unmapped_rows:
        print("unmapped files: " + ", ".join(unmapped_rows))
    if missing_rows:
        print("upstream-missing files: " + ", ".join(missing_rows))
    if native_rows:
        print("native files: " + ", ".join(native_rows))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
