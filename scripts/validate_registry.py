#!/usr/bin/env python3
"""Validate the canonical Navier attack registry."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from registry_core import RegistryValidationError, compiler_owned_status_file


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("registry", type=Path, help="Path to attack_registry.json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        data, status = compiler_owned_status_file(args.registry)
    except RegistryValidationError as exc:
        print(f"INVALID {args.registry} ({len(exc.errors)} error(s))", file=sys.stderr)
        for error in exc.errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"INVALID {args.registry}: {exc}", file=sys.stderr)
        return 1
    print(
        "VALID "
        f"registry={data['registry_id']}@{data['registry_version']} "
        f"approaches={len(data['approaches'])} "
        f"obligations={len(data['obligations'])} "
        f"status={status['global_disposition']}/{status['scientific_status']} "
        f"authority={status['status_authority']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
