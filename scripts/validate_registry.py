#!/usr/bin/env python3
"""Validate the canonical Navier attack registry."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from registry_core import validate_registry_file


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("registry", type=Path, help="Path to attack_registry.json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        data, result = validate_registry_file(args.registry)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"INVALID {args.registry}: {exc}", file=sys.stderr)
        return 1
    if not result.valid:
        print(f"INVALID {args.registry} ({len(result.errors)} error(s))", file=sys.stderr)
        for error in result.errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(
        "VALID "
        f"registry={data['registry_id']}@{data['registry_version']} "
        f"approaches={len(data['approaches'])} "
        f"obligations={len(data['obligations'])} "
        f"status={data['research_program']['global_disposition']}/"
        f"{data['research_program']['scientific_status']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
