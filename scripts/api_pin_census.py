#!/usr/bin/env python3
"""api_pin_census.py — name-by-name comparison of Navier.APIPin against the compiler's own declaration environment.

Closes the blind spot measured in Navier/APIPin.lean's coverage guard: the old
generating census was `grep -cE '^\\s*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\\b'`,
whose anchored keyword alternation does not match modifier-prefixed lines
(`noncomputable def …`, `protected def …`), so those exported names silently
fell out of the pin contract.

The denominator here is the compiler: `lake env lean scripts/ApiEnvCensus.lean`
enumerates every declaration in the Lean environment whose fully qualified name
starts with one of the two T0 module prefixes. A source-declaration scan of the
two module files (namespace-stack aware, modifier tolerant) classifies each
compiler name as source-declared API or compiler-generated auxiliary; only
source-declared names enter the pin contract. Anonymous instances (`instance : T`)
have no stable name and are not pinned.

Exit codes: 0 = pins and compiler census agree exactly; 1 = missing or stale
pins (printed one per line); 2 = environment failure.

Usage (from the repository root, with built .lake artifacts):
  python3 scripts/api_pin_census.py                 # run the census itself
  python3 scripts/api_pin_census.py --names FILE    # names already dumped (one per line)
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

MODULES = {
    "Navier/Analysis/ContinuousLeiLinSpace.lean": "Navier.Analysis.ContinuousLeiLinSpace",
    "Navier/Construction/PeriodizedWaveBounds.lean": "Navier.Construction.PeriodizedWaveBounds",
}
PIN_FILE = "Navier/APIPin.lean"

MODIFIERS = r"(?:(?:private|protected|noncomputable|partial|unsafe|deprecated)\s+)*"
KEYWORDS = r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)"
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?" + MODIFIERS + KEYWORDS + r"\s+([^\s:(\[={;|,]+)"
)
# named instance: `instance foo :` or `instance foo {…} :` or `instance foo [priority]...`
BARE_INSTANCE_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?" + MODIFIERS + r"instance\s*(?::|\(|\{|\[)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([\w.·]+)")
END_RE = re.compile(r"^\s*end(?:\s+([\w.·]+))?\s*$")


def mask_comments(text: str) -> str:
    """Replace Lean line and (nestable) block comments with spaces, keeping line structure."""
    out = []
    i, n = 0, len(text)
    depth = 0
    in_str = False
    in_char = False
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
                continue
            if c == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append(c if c == "\n" else " ")
            i += 1
            continue
        if in_str:
            out.append(c if c == "\n" else " ")
            if c == "\\":
                out.append(" ")
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if in_char:
            out.append(c if c == "\n" else " ")
            if c == "'":
                in_char = False
            i += 1
            continue
        if c == "/" and nxt == "-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if c == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if c == '"':
            in_str = True
            out.append(" ")
            i += 1
            continue
        if c == "'":
            # char literal only in argument position; identifier primes (foo') are not
            prev = out[-1] if out else " "
            if prev in "=(,[ \t" and i + 2 < n and text[i + 1] != " " and text[i + 2] == "'":
                out.append(" ")
                i += 3
                continue
            out.append(c)
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def source_names(root: Path) -> set[str]:
    out: set[str] = set()
    for rel, prefix in MODULES.items():
        text = mask_comments((root / rel).read_text())
        stack: list[str] = []
        for line in text.splitlines():
            s = line.strip()
            if not s:
                continue
            ns = NAMESPACE_RE.match(line)
            if ns:
                stack.append(ns.group(1))
                continue
            end = END_RE.match(line)
            if end:
                if end.group(1) is None or (stack and stack[-1].split(".")[-1] == end.group(1).split(".")[-1]):
                    if stack:
                        stack.pop()
                continue
            if BARE_INSTANCE_RE.match(line):
                continue  # anonymous instance: compiler-generated name, not pinnable
            m = DECL_RE.match(line)
            if not m:
                continue
            # `private` declarations are not public API: outside the namespace no
            # consumer can reference them, so they are not pinnable.
            head = line[: m.start(1)]
            if re.search(r"\bprivate\b", head):
                continue
            name = m.group(1)
            # a nested `end` line may close several namespaces at once ("end Foo Bar") —
            # handled above conservatively; names are qualified with the current stack
            full = ".".join(stack + [name]) if stack else name
            if full.startswith(prefix + "."):
                out.add(full)
        # names declared before/after the file namespace, outside prefix, are not exported API
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".", help="repository root (default: cwd)")
    ap.add_argument("--names", help="file with compiler-env names, one per line (skips running lake)")
    args = ap.parse_args()
    root = Path(args.root).resolve()

    if args.names:
        raw = Path(args.names).read_text().splitlines()
        census = {l.strip() for l in raw if l.strip() and "." in l and not l.startswith(("TOTAL", "/", "error"))
                  and " " not in l.strip()}
    else:
        probe = root / "scripts" / "ApiEnvCensus.lean"
        r = subprocess.run(["lake", "env", "lean", str(probe)], cwd=root, capture_output=True, text=True)
        if r.returncode != 0:
            sys.stderr.write(r.stderr[-2000:])
            print(f"census run failed rc={r.returncode}")
            return 2
        census = {l.strip() for l in r.stdout.splitlines() if l.strip() and "." in l
                  and not l.startswith(("TOTAL", "/", "error")) and " " not in l.strip()}

    pins = set(re.findall(r"#check @([^\s]+)", mask_comments((root / PIN_FILE).read_text())))
    api = source_names(root)

    api_present = api & census
    missing_src_in_env = api - census  # source declares it but env has no such name (suspicious)
    aux = {n for n in census if n not in api}
    missing = sorted(api_present - pins)
    stale = sorted(pins - census)
    print(f"env_names={len(census)} source_declared={len(api)} api_in_env={len(api_present)} "
          f"pinned={len(pins)} generated_excluded={len(aux)} missing_pins={len(missing)} "
          f"stale_pins={len(stale)} source_absent_from_env={len(missing_src_in_env)}")
    for n in missing:
        print(f"MISSING {n}")
    for n in stale:
        print(f"STALE {n}")
    for n in sorted(missing_src_in_env):
        print(f"SRC-NO-ENV {n}")
    return 1 if (missing or stale or missing_src_in_env) else 0


if __name__ == "__main__":
    sys.exit(main())
