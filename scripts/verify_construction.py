#!/usr/bin/env python3
"""Rebuild C or source-audit the exact A/B/C/D regularity endpoints.

This deliberately compiles source files one at a time.  It does not call an
umbrella Lake build and does not infer proof status from source text.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Iterable, Mapping, NamedTuple


DEFAULT_ROOT_MODULE = "Navier.Breakdown.ConstructedBreakdown"
ENDPOINT = "Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown"
AUDITED_DECLARATIONS = (
    ENDPOINT,
    "Navier.Analysis.ConstructedForceExtension.constructedWholeSpaceBreakdownWithGloballySmoothForce",
    "Navier.Analysis.ForceRecursivePartials.forcedDataRapidDecay_bounds_successivePartials",
    "Navier.Breakdown.ConstructedBreakdown.wholeSpaceBreakdown_with_successivePartials",
    "Navier.Breakdown.ConstructedBreakdown.selectedFiniteEnergyCandidate",
    "Navier.Analysis.ForceCoordinateEquivalence.forcedDataRapidDecay_iff_successivePartials",
    "Navier.Analysis.ForceCoordinateEquivalence.periodicForcedDataRapidDecay_iff_successivePartials",
    "Navier.Construction.ComparatorBridge.compact_candidate_unique_on_Icc",
    "Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_finite_time_profile",
    "Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_no_continuous_extension",
    "Navier.Analysis.ConstructedFiniteTimeObstruction.selected_candidate_excludes_locally_finite_energy_continuation",
)
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

ENDPOINT_TARGETS = {
    "A": "Navier.ProblemStatements.WholeSpaceGlobalRegularity",
    "B": "Navier.ProblemStatements.PeriodicGlobalRegularity",
    "C": "Navier.ProblemStatements.WholeSpaceBreakdown",
    "D": "Navier.ProblemStatements.PeriodicBreakdown",
}

# These are acceptance boundaries for interpreting compiler-clean declarations.
# They do not replace the exact Lean type check performed for a witness below.
ENDPOINT_SCIENTIFIC_LIMITS = {
    "A": (
        "consumer requires a smooth unforced whole-space velocity-pressure pair "
        "for every admissible Schwartz datum and every positive viscosity"
    ),
    "B": (
        "consumer requires a real smooth period-one velocity and pressure; a raw "
        "complex lattice mild equation must supply conjugate symmetry, reconstruction, "
        "A=-2*pi*I*u_hat, and mu=(2*pi)^2*nu before it can discharge this endpoint"
    ),
    "C": (
        "consumer requires, for every positive viscosity, admissible whole-space datum "
        "and rapidly decaying force excluding every global classical solution pair"
    ),
    "D": (
        "consumer requires, for every positive viscosity, admissible periodic datum "
        "and periodic rapidly decaying force excluding every global periodic pair"
    ),
}


class EndpointAuditItem(NamedTuple):
    label: str
    kind: str
    module: str
    declaration: str


DEFAULT_ENDPOINT_AUDIT_ITEMS = (
    EndpointAuditItem(label, "proposition", "Navier.OfficialProblem", declaration)
    for label, declaration in ENDPOINT_TARGETS.items()
)
DEFAULT_ENDPOINT_AUDIT_ITEMS = tuple(DEFAULT_ENDPOINT_AUDIT_ITEMS) + (
    EndpointAuditItem(
        "A", "signature", "Navier.OfficialSurfaceSignatures",
        "Navier.OfficialSurfaceSignatures.wholeSpaceGlobalRegularity_signature",
    ),
    EndpointAuditItem(
        "B", "signature", "Navier.OfficialSurfaceSignatures",
        "Navier.OfficialSurfaceSignatures.periodicGlobalRegularity_signature",
    ),
    EndpointAuditItem(
        "C", "signature", "Navier.OfficialSurfaceSignatures",
        "Navier.OfficialSurfaceSignatures.wholeSpaceBreakdown_signature",
    ),
    EndpointAuditItem(
        "D", "signature", "Navier.OfficialSurfaceSignatures",
        "Navier.OfficialSurfaceSignatures.periodicBreakdown_signature",
    ),
    EndpointAuditItem(
        "A", "conditional", "Navier.Analysis.CriticalControlDecomposition",
        "Navier.Analysis.CriticalControlDecomposition."
        "wholeSpaceGlobalRegularity_of_local_continuation_apriori",
    ),
    EndpointAuditItem(
        "B", "reduction", "Navier.Analysis.ViscosityEndpoints",
        "Navier.Analysis.ViscosityEndpoints.periodicGlobalRegularity_iff_atViscosityOne",
    ),
    EndpointAuditItem(
        "C", "reduction", "Navier.Analysis.ViscosityEndpoints",
        "Navier.Analysis.ViscosityEndpoints.wholeSpaceBreakdown_iff_atViscosityOne",
    ),
    EndpointAuditItem(
        "D", "conditional", "Navier.Analysis.ViscosityEndpoints",
        "Navier.Analysis.ViscosityEndpoints.periodicBreakdown_of_zeroForceAtViscosityOne",
    ),
    EndpointAuditItem(
        "C", "witness", "Navier.Breakdown.ConstructedBreakdown",
        ENDPOINT,
    ),
    EndpointAuditItem(
        "D", "witness", "Navier.Analysis.PeriodicConstructedBreakdown",
        "Navier.Analysis.PeriodicConstructedBreakdown.periodicBreakdown",
    ),
)


class VerificationError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def strip_lean_comments(source: str) -> str:
    """Replace nested Lean comments with whitespace while preserving lines."""
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(source):
        if depth == 0 and source.startswith("--", i):
            end = source.find("\n", i)
            if end == -1:
                out.extend(" " * (len(source) - i))
                break
            out.extend(" " * (end - i))
            i = end
        elif source.startswith("/-", i):
            depth += 1
            out.extend("  ")
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            out.extend("  ")
            i += 2
        else:
            char = source[i]
            out.append(char if depth == 0 or char == "\n" else " ")
            i += 1
    if depth:
        raise VerificationError("unterminated block comment")
    return "".join(out)


def imports_from_source(source: str) -> list[str]:
    clean = strip_lean_comments(source)
    imports: list[str] = []
    for match in re.finditer(r"(?m)^\s*(?:public\s+)?import\s+([^\n]+)$", clean):
        imports.extend(match.group(1).split())
    return imports


def module_path(project_root: Path, module: str) -> Path:
    return project_root / (module.replace(".", "/") + ".lean")


def local_import_graph(project_root: Path, root_module: str) -> dict[str, list[str]]:
    """Return only the local import closure reachable from ``root_module``."""
    graph: dict[str, list[str]] = {}

    def visit(module: str) -> None:
        if module in graph:
            return
        path = module_path(project_root, module)
        if not path.is_file():
            raise VerificationError(f"local root module has no source: {module} ({path})")
        local = []
        for imported in imports_from_source(path.read_text(encoding="utf-8")):
            if module_path(project_root, imported).is_file():
                local.append(imported)
        graph[module] = local
        for imported in local:
            visit(imported)

    visit(root_module)
    return graph


def dependency_order(graph: Mapping[str, Iterable[str]], root_module: str) -> list[str]:
    order: list[str] = []
    permanent: set[str] = set()
    active: list[str] = []

    def visit(module: str) -> None:
        if module in permanent:
            return
        if module in active:
            cycle = active[active.index(module) :] + [module]
            raise VerificationError("local import cycle: " + " -> ".join(cycle))
        if module not in graph:
            raise VerificationError(f"missing local graph node: {module}")
        active.append(module)
        for dependency in graph[module]:
            visit(dependency)
        active.pop()
        permanent.add(module)
        order.append(module)

    visit(root_module)
    return order


def environment_fingerprint(project_root: Path) -> str:
    inputs = {}
    for name in ("lean-toolchain", "lakefile.toml", "lakefile.lean", "lake-manifest.json"):
        path = project_root / name
        if path.is_file():
            inputs[name] = sha256(path.read_bytes())
    if "lean-toolchain" not in inputs:
        raise VerificationError("lean-toolchain is required")
    if "lakefile.toml" not in inputs and "lakefile.lean" not in inputs:
        raise VerificationError("a Lake project file is required")
    return sha256(json.dumps(inputs, sort_keys=True).encode())


def compute_fingerprints(
    project_root: Path,
    graph: Mapping[str, list[str]],
    order: Iterable[str],
    environment: str,
) -> dict[str, dict[str, object]]:
    result: dict[str, dict[str, object]] = {}
    for module in order:
        path = module_path(project_root, module)
        source_digest = sha256(path.read_bytes())
        dependencies = {name: result[name]["fingerprint"] for name in graph[module]}
        payload = {
            "source_sha256": source_digest,
            "dependency_fingerprints": dependencies,
            "environment_fingerprint": environment,
        }
        result[module] = {**payload, "fingerprint": sha256(json.dumps(payload, sort_keys=True).encode())}
    return result


def load_receipts(path: Path) -> dict[str, dict[str, object]]:
    if not path.exists():
        return {}
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise VerificationError(f"cannot read receipts {path}: {error}") from error
    if not isinstance(value, dict):
        raise VerificationError(f"receipt file is not a JSON object: {path}")
    return value


def fresh_modules(
    modules: Iterable[str],
    graph: Mapping[str, Iterable[str]],
    fingerprints: Mapping[str, Mapping[str, object]],
    receipts: Mapping[str, Mapping[str, object]],
    olean_root: Path,
) -> set[str]:
    fresh = set()
    for module in modules:
        output = olean_root / (module.replace(".", "/") + ".olean")
        if (
            all(dependency in fresh for dependency in graph[module])
            and output.is_file()
            and receipts.get(module, {}).get("exit_code") == 0
            and receipts.get(module, {}).get("fingerprint") == fingerprints[module]["fingerprint"]
            and receipts.get(module, {}).get("output_sha256") == sha256(output.read_bytes())
        ):
            fresh.add(module)
    return fresh


def parse_axioms(output: str, declaration: str) -> set[str]:
    escaped = re.escape(declaration)
    match = re.search(rf"'{escaped}' depends on axioms:\s*\[([^\]]*)\]", output, re.DOTALL)
    if match:
        return {item.strip() for item in match.group(1).split(",") if item.strip()}
    if re.search(rf"'{escaped}' does not depend on any axioms", output):
        return set()
    raise VerificationError(f"could not parse raw #print axioms output for {declaration}")


def parse_endpoint_witness(value: str) -> EndpointAuditItem:
    """Parse ``LABEL=MODULE:DECLARATION`` without inferring endpoint status."""
    match = re.fullmatch(r"([A-D])=([A-Za-z0-9_.]+):([A-Za-z0-9_.]+)", value)
    if not match:
        raise argparse.ArgumentTypeError(
            "endpoint witness must be LABEL=MODULE:DECLARATION with LABEL in A..D"
        )
    label, module, declaration = match.groups()
    return EndpointAuditItem(label, "witness", module, declaration)


def parse_endpoint_prerequisite(value: str) -> EndpointAuditItem:
    """Parse a checked analytic component without promoting it to an endpoint witness."""
    match = re.fullmatch(r"([A-D])=([A-Za-z0-9_.]+):([A-Za-z0-9_.]+)", value)
    if not match:
        raise argparse.ArgumentTypeError(
            "endpoint prerequisite must be LABEL=MODULE:DECLARATION with LABEL in A..D"
        )
    label, module, declaration = match.groups()
    return EndpointAuditItem(label, "prerequisite", module, declaration)


def require_module_source(project_root: Path, module: str, olean_root: Path) -> Path:
    """Require current source; an object by itself is never endpoint evidence."""
    source = module_path(project_root, module)
    if source.is_file():
        return source
    output = olean_root / (module.replace(".", "/") + ".olean")
    if output.is_file():
        raise VerificationError(
            f"object-only endpoint provider is stale evidence: {module} has {output} but no {source}"
        )
    raise VerificationError(f"endpoint provider has no local source: {module} ({source})")


def endpoint_audit_source(source: str, items: Iterable[EndpointAuditItem]) -> str:
    """Append checks to the provider source so its existing object cannot mask edits."""
    audited_items = tuple(items)
    # A provider need not import the official endpoint definitions.  Put the
    # original consumer in scope before recompiling the provider so a witness
    # check fails on its type rather than on an unavailable target name.
    commands = [] if all(
        item.module == "Navier.OfficialProblem" for item in audited_items
    ) else ["import Navier.OfficialProblem"]
    commands.extend((source, "", "/- generated focused endpoint audit -/"))
    for index, item in enumerate(audited_items):
        commands.extend((
            f"#check {item.declaration}",
            f"#print {item.declaration}",
            f"#print axioms {item.declaration}",
        ))
        if item.kind == "proposition":
            commands.append(f"#check ({item.declaration} : Prop)")
        elif item.kind == "witness":
            commands.append(
                f"example : {ENDPOINT_TARGETS[item.label]} := {item.declaration}"
            )
        commands.append(f"-- endpoint-audit-item {index} {item.label} {item.kind}")
    return "\n".join(commands) + "\n"


def endpoint_audit_command(
    source: Path, lock_wrapper: Path | None, lock_timeout: int
) -> list[str]:
    command = ["lake", "env", "lean", str(source)]
    if lock_wrapper is None:
        return command
    return [str(lock_wrapper), str(lock_timeout), *command]


def source_closure_freshness(
    project_root: Path,
    module: str,
    receipts_path: Path,
    olean_root: Path,
) -> tuple[bool, str]:
    """Check fingerprinted dependency receipts without rebuilding anything."""
    graph = local_import_graph(project_root, module)
    order = dependency_order(graph, module)
    environment = environment_fingerprint(project_root)
    fingerprints = compute_fingerprints(project_root, graph, order, environment)
    receipts = load_receipts(receipts_path)
    fresh = fresh_modules(order, graph, fingerprints, receipts, olean_root)
    return module in fresh, f"{len(fresh)}/{len(order)}"


def endpoint_audit_status(
    label: str, source_checked_witnesses: set[str], fresh_witnesses: set[str]
) -> str:
    if label in fresh_witnesses:
        return "UNCONDITIONAL-WITNESS-VERIFIED"
    if label in source_checked_witnesses:
        return "WITNESS-SOURCE-CHECKED-DEPENDENCY-FRESHNESS-NOT-ESTABLISHED"
    return "NO-UNCONDITIONAL-WITNESS-IN-THIS-AUDIT"


def run_regularity_endpoint_audit(args: argparse.Namespace) -> int:
    """Compile exact provider sources and classify only explicit witnesses as closure."""
    project_root = args.project_root.resolve()
    verify_compiler(project_root)
    if args.lock_wrapper is not None:
        if not args.lock_wrapper.is_file() or not os.access(args.lock_wrapper, os.X_OK):
            raise VerificationError(f"lock wrapper is not executable: {args.lock_wrapper}")

    items = (
        DEFAULT_ENDPOINT_AUDIT_ITEMS
        + tuple(args.endpoint_prerequisite)
        + tuple(args.endpoint_witness)
    )
    by_module: dict[str, list[EndpointAuditItem]] = {}
    for item in items:
        by_module.setdefault(item.module, []).append(item)

    source_checked_witnesses: set[str] = set()
    fresh_witnesses: set[str] = set()
    args.log_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="navier-endpoint-audit-") as directory:
        audit_root = Path(directory)
        for module, module_items in by_module.items():
            source = require_module_source(project_root, module, args.olean_root)
            source_bytes = source.read_bytes()
            audit_source = audit_root / (module.replace(".", "-") + ".lean")
            audit_source.write_text(
                endpoint_audit_source(source_bytes.decode("utf-8"), module_items),
                encoding="utf-8",
            )
            command = endpoint_audit_command(
                audit_source, args.lock_wrapper, args.lock_timeout
            )
            result = subprocess.run(
                command,
                cwd=project_root,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=args.timeout,
            )
            log = args.log_dir / ("endpoint-" + module + ".log")
            log.write_text(result.stdout, encoding="utf-8")
            if source.read_bytes() != source_bytes:
                raise VerificationError(f"source changed during endpoint audit: {module}")
            if result.returncode:
                raise VerificationError(
                    f"current-source endpoint audit failed for {module}; see {log}"
                )
            print(f"SOURCE-CHECKED {module} sha256={sha256(source_bytes)}")
            for item in module_items:
                axioms = parse_axioms(result.stdout, item.declaration)
                unexpected = axioms - ALLOWED_AXIOMS
                if unexpected:
                    raise VerificationError(
                        item.declaration + " uses nonstandard axioms: "
                        + ", ".join(sorted(unexpected))
                    )
                print(
                    f"AUDITED {item.label} kind={item.kind} declaration={item.declaration} "
                    f"axioms={','.join(sorted(axioms))}"
                )
                if item.kind in {"prerequisite", "witness"}:
                    is_fresh, fraction = source_closure_freshness(
                        project_root,
                        item.module,
                        args.receipts,
                        args.olean_root,
                    )
                    print(
                        f"{item.kind.upper()}-EVIDENCE {item.label} current_source=yes "
                        f"type_and_axioms=yes dependency_receipts={fraction} "
                        f"endpoint_witness={'yes' if item.kind == 'witness' else 'no'}"
                    )
                    if item.kind == "witness":
                        source_checked_witnesses.add(item.label)
                        if is_fresh:
                            fresh_witnesses.add(item.label)

    for label, target in ENDPOINT_TARGETS.items():
        status = endpoint_audit_status(
            label, source_checked_witnesses, fresh_witnesses
        )
        print(f"ENDPOINT {label} target={target} status={status}")
        print(f"SCIENTIFIC-LIMIT {label} {ENDPOINT_SCIENTIFIC_LIMITS[label]}")
    return 0


def atomic_write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", dir=path.parent, delete=False) as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")
        temporary = Path(stream.name)
    temporary.replace(path)


def command_for(source: Path, output: Path, lock_wrapper: Path | None, lock_timeout: int) -> list[str]:
    lean = ["lake", "env", "lean", "-o", str(output), str(source)]
    if lock_wrapper is None:
        return lean
    return [str(lock_wrapper), str(lock_timeout), *lean]


def verify_compiler(project_root: Path) -> str:
    expected = (project_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    result = subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=project_root,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    if result.returncode:
        raise VerificationError("lake env lean --version failed:\n" + result.stdout)
    match = re.search(r":v([^\s]+)$", expected)
    if match and f"version {match.group(1)}" not in result.stdout:
        raise VerificationError(f"compiler does not match {expected}: {result.stdout.strip()}")
    return result.stdout.strip()


def run(args: argparse.Namespace) -> int:
    project_root = args.project_root.resolve()
    graph = local_import_graph(project_root, args.root_module)
    order = dependency_order(graph, args.root_module)
    environment = environment_fingerprint(project_root)
    fingerprints = compute_fingerprints(project_root, graph, order, environment)
    receipts = load_receipts(args.receipts)
    fresh = set() if args.force else fresh_modules(order, graph, fingerprints, receipts, args.olean_root)

    print(f"root={args.root_module}")
    print(f"local_closure={len(order)} fresh={len(fresh)} rebuild={len(order) - len(fresh)}")
    if args.check_plan:
        for module in order:
            print(("FRESH " if module in fresh else "BUILD ") + module)
        return 0

    compiler_version = verify_compiler(project_root)
    print("compiler=" + compiler_version)
    args.log_dir.mkdir(parents=True, exist_ok=True)
    args.olean_root.mkdir(parents=True, exist_ok=True)
    if args.lock_wrapper is not None:
        if not args.lock_wrapper.is_file() or not os.access(args.lock_wrapper, os.X_OK):
            raise VerificationError(f"lock wrapper is not executable: {args.lock_wrapper}")

    completed = set(fresh)
    pending = [module for module in order if module not in completed]
    running: dict[concurrent.futures.Future[tuple[str, dict[str, object], str]], str] = {}
    failure: tuple[str, dict[str, object], str] | None = None
    compile_env = dict(os.environ)

    def compile_one(module: str) -> tuple[str, dict[str, object], str]:
        source = module_path(project_root, module)
        before = source.read_bytes()
        output = args.olean_root / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = args.log_dir / (module + ".log")
        command = command_for(source.relative_to(project_root), output, args.lock_wrapper, args.lock_timeout)
        result = subprocess.run(
            command, cwd=project_root, env=compile_env, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=args.timeout,
        )
        log.write_text(result.stdout, encoding="utf-8")
        if source.read_bytes() != before:
            raise VerificationError(f"source changed during compilation: {module}")
        receipt = {
            **fingerprints[module],
            "exit_code": result.returncode,
            "command": command,
            "log": os.path.relpath(log, project_root),
            "output": os.path.relpath(output, project_root),
            "output_sha256": sha256(output.read_bytes()) if result.returncode == 0 else None,
        }
        return module, receipt, result.stdout

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            for module in list(pending):
                if failure is not None or len(running) >= args.jobs:
                    break
                if all(dependency in completed for dependency in graph[module]):
                    pending.remove(module)
                    running[pool.submit(compile_one, module)] = module
            if not running:
                break
            done, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for task in done:
                running.pop(task)
                module, receipt, output = task.result()
                if receipt["exit_code"]:
                    failure = (module, receipt, output)
                    print(f"FAILED {module} exit={receipt['exit_code']}", file=sys.stderr)
                    print(output[-10000:], file=sys.stderr)
                else:
                    receipts[module] = receipt
                    completed.add(module)
                    atomic_write_json(args.receipts, receipts)
                    print(f"CHECKED {len(completed)}/{len(order)} {module}")
        if failure is not None:
            return 1
    if pending:
        raise VerificationError("dependency scheduler stalled: " + ", ".join(pending[:10]))

    if args.materialize_only:
        print(f"MATERIALIZED {args.root_module} current_dependency_receipts={len(order)}/{len(order)}")
        print("No endpoint claim audited; use --audit-regularity-endpoints with the exact witness.")
        return 0

    audit_source = args.receipts.parent / "ConstructedBreakdownAudit.lean"
    audit_source.parent.mkdir(parents=True, exist_ok=True)
    audit_commands = [
        f"import {args.root_module}",
        "example : Navier.ProblemStatements.WholeSpaceBreakdown := " + ENDPOINT,
    ]
    for declaration in AUDITED_DECLARATIONS:
        audit_commands.extend((
            f"#check {declaration}",
            f"#print {declaration}",
            f"#print axioms {declaration}",
        ))
    audit_source.write_text("\n".join(audit_commands) + "\n", encoding="utf-8")
    audit_output = args.receipts.parent / "ConstructedBreakdownAudit.olean"
    audit_command = command_for(audit_source, audit_output, args.lock_wrapper, args.lock_timeout)
    audit = subprocess.run(
        audit_command, cwd=project_root, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=args.timeout,
    )
    audit_log = args.log_dir / "ConstructedBreakdownAudit.log"
    audit_log.write_text(audit.stdout, encoding="utf-8")
    print(audit.stdout, end="")
    if audit.returncode:
        raise VerificationError(f"endpoint audit failed; see {audit_log}")
    for declaration in AUDITED_DECLARATIONS:
        axioms = parse_axioms(audit.stdout, declaration)
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            raise VerificationError(
                declaration + " uses nonstandard axioms: " + ", ".join(sorted(unexpected))
            )
        print("VERIFIED " + declaration + " axioms=" + ",".join(sorted(axioms)))
    return 0


def parser() -> argparse.ArgumentParser:
    project_root = Path(__file__).resolve().parents[1]
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--project-root", type=Path, default=project_root)
    result.add_argument("--root-module", default=DEFAULT_ROOT_MODULE)
    result.add_argument("--jobs", type=int, default=2)
    result.add_argument("--timeout", type=int, default=900, help="seconds per source file")
    result.add_argument("--lock-wrapper", type=Path, help="optional executable prepended as WRAPPER TIMEOUT COMMAND...")
    result.add_argument("--lock-timeout", type=int, default=600)
    result.add_argument("--receipts", type=Path)
    result.add_argument("--log-dir", type=Path)
    result.add_argument("--olean-root", type=Path)
    result.add_argument("--check-plan", "--dry-run", action="store_true", dest="check_plan")
    result.add_argument("--force", action="store_true")
    result.add_argument(
        "--materialize-only", action="store_true",
        help="refresh the selected root's source dependencies without making an endpoint proof claim",
    )
    result.add_argument(
        "--audit-regularity-endpoints",
        action="store_true",
        help="source-compile and classify the exact A/B/C/D endpoint surfaces",
    )
    result.add_argument(
        "--endpoint-prerequisite",
        action="append",
        default=[],
        type=parse_endpoint_prerequisite,
        metavar="LABEL=MODULE:DECLARATION",
        help="source-audit an analytic component without claiming endpoint closure",
    )
    result.add_argument(
        "--endpoint-witness",
        action="append",
        default=[],
        type=parse_endpoint_witness,
        metavar="LABEL=MODULE:DECLARATION",
        help="add a claimed unconditional endpoint witness to the focused audit",
    )
    return result


def main() -> int:
    args = parser().parse_args()
    if args.jobs < 1:
        print("verification error: --jobs must be positive", file=sys.stderr)
        return 2
    args.project_root = args.project_root.resolve()
    state = args.project_root / ".lake" / "verify-construction"
    args.receipts = args.receipts or state / "receipts.json"
    args.log_dir = args.log_dir or state / "logs"
    args.olean_root = args.olean_root or args.project_root / ".lake" / "build" / "lib" / "lean"
    for name in ("receipts", "log_dir", "olean_root"):
        path = getattr(args, name)
        if not path.is_absolute():
            setattr(args, name, (args.project_root / path).resolve())
    if args.lock_wrapper is not None and not args.lock_wrapper.is_absolute():
        args.lock_wrapper = (Path.cwd() / args.lock_wrapper).resolve()
    try:
        if args.audit_regularity_endpoints:
            return run_regularity_endpoint_audit(args)
        return run(args)
    except (VerificationError, subprocess.TimeoutExpired) as error:
        print(f"verification error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
