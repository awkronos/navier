#!/usr/bin/env python3
"""Status-vocabulary sweep over repository markdown (docs hygiene aid).

research-mathematics.md §2: status prose that names a residual must be checked
against current source, because inspection misses and a stale sentence
propagates a false premise to every lane dispatched from it. This script
enumerates the hits; it does NOT adjudicate them.

Adjudication is human/compiler work:
  * a hit that names a Lean declaration is heuristically annotated PRESENT /
    MISSING by a literal-name scan of Navier/ sources. PRESENT is not proof
    the obligation discharged; MISSING (for a name appearing in no source
    file) is a strong staleness signal. Compiler probe is authority for any
    closure claim — see scripts/check_formalization.py and AxiomAudit.lean.

Usage:
  python3 scripts/status_vocab_sweep.py [--check-decls] [--root DIR]
                                        [--pattern REGEX]
Exit code is 0 unless --strict-decls is passed, in which case a MISSING-named
decleration hit exits 1 (for optional CI use).
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

DEFAULT_VOCAB = (
    r"residual|modulo|remains|not yet|no longer|ceiling|impossible|"
    r"out of reach|open forever|superseded|removed in the soundness"
)

# dated receipt archives are historical records, not live status surfaces;
# sweep them explicitly with --root reports
SKIP_DIR_PARTS = {".lake", ".git", "artifacts", "references", "__pycache__", "reports"}


def iter_markdown(root: Path):
    for path in sorted(root.rglob("*.md")):
        if SKIP_DIR_PARTS.intersection(path.relative_to(root).parts):
            continue
        yield path


def build_name_index(root: Path) -> set[str]:
    """Literal set of backtick-quoteable identifier tokens in Lean sources."""
    names: set[str] = set()
    lean_root = root / "Navier"
    if not lean_root.is_dir():
        return names
    ident = re.compile(r"[A-Za-z_][A-Za-z0-9_.'*‾]*")
    for f in lean_root.rglob("*.lean"):
        try:
            text = f.read_text(encoding="utf-8")
        except OSError:
            continue
        # cheap prefilter: only tokenize lines that look declarative
        for line in text.splitlines():
            if re.match(r"\s*(theorem|lemma|def|example|abbrev)\b", line):
                m = re.match(
                    r"\s*(?:theorem|lemma|def|example|abbrev)\s+([A-Za-z_][\w.'*‾]*)",
                    line,
                )
                if m:
                    names.add(m.group(1).rstrip(".'*‾"))
    return names


BACKTICK = re.compile(r"`([^`]+)`")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", default=".", type=Path)
    ap.add_argument("--pattern", default=DEFAULT_VOCAB)
    ap.add_argument(
        "--check-decls",
        action="store_true",
        help="annotate hits whose backticked tokens look like Lean names",
    )
    ap.add_argument(
        "--strict-decls",
        action="store_true",
        help="like --check-decls but exit 1 if any named decl is absent from source",
    )
    args = ap.parse_args()

    root = args.root.resolve()
    vocab = re.compile(args.pattern, re.IGNORECASE)
    decl_names: set[str] = set()
    if args.check_decls or args.strict_decls:
        decl_names = build_name_index(root)

    missing_hits = 0
    total = 0
    for path in iter_markdown(root):
        rel = path.relative_to(root)
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if not vocab.search(line):
                continue
            total += 1
            note = ""
            if args.check_decls or args.strict_decls:
                # dotted lowerCamel backticked tokens only; single-word tokens
                # are English or field names, not fully qualified declarations
                cands = [t for t in BACKTICK.findall(line) if re.fullmatch(r"[a-z][\w']*(?:\.[a-z][\w']*)+", t)]
                checked = []
                for t in cands:
                    short = t.split(".")[-1]
                    present = t in decl_names or short in decl_names
                    checked.append(f"{t}:{'PRESENT' if present else 'MISSING'}")
                    if not present:
                        missing_hits += 1
                if checked:
                    note = "  [" + " ".join(checked) + "]"
            print(f"{rel}:{i}: {line.strip()[:160]}{note}")

    print(f"\n{total} status-vocabulary hit(s). Each must be adjudicated against"
          f" the elaborated signature or current file state it names.", file=sys.stderr)
    if args.strict_decls and missing_hits:
        print(f"{missing_hits} backticked name(s) absent from Navier/ sources.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
