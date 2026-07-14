#!/usr/bin/env python3
"""Render status derived exclusively from the canonical attack registry."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from registry_core import derived_status, validate_registry_file


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("registry", type=Path, help="Path to attack_registry.json")
    parser.add_argument("--json", action="store_true", help="Emit the derived view as JSON")
    return parser


def _render_text(status: dict[str, object]) -> str:
    lines = [
        "NAVIER ATTACK STATUS (derived; registry is the SSOT)",
        f"registry: {status['registry_id']}@{status['registry_version']}",
        f"base revision: {status['base_revision']}",
        f"global: {status['global_disposition']} / {status['scientific_status']}",
        "endpoints:",
    ]
    for endpoint in status["endpoints"]:  # type: ignore[union-attr]
        lines.append(
            f"  {endpoint['branch']}: {endpoint['disposition']} ({endpoint['id']})"
        )
        if endpoint["residual"]:
            lines.append(f"    residual: {endpoint['residual']}")
    lines.append("approaches:")
    for approach in status["approaches"]:  # type: ignore[union-attr]
        blocked = ",".join(approach["blocked_barriers"]) or "none"
        lines.append(
            f"  {approach['id']}: {approach['status']}; "
            f"nodes={approach['obligation_count']} closed={approach['closed']} "
            f"open={approach['open']} blocked={blocked}"
        )
    lines.append(f"dispositions: {json.dumps(status['dispositions'], sort_keys=True)}")
    lines.append(f"claim tiers: {json.dumps(status['claim_tiers'], sort_keys=True)}")
    return "\n".join(lines)


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
    status = derived_status(data)
    if args.json:
        print(json.dumps(status, indent=2, sort_keys=True))
    else:
        print(_render_text(status))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
