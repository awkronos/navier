"""Fail-closed validation and derived status for the Navier attack registry.

The validator intentionally uses only the Python standard library.  The JSON
Schema is the interchange contract; this module enforces the same closed-world
shape plus graph, provenance, epistemic, and native-receipt invariants that
JSON Schema alone cannot express.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
import subprocess
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Iterable


SCHEMA_VERSION = "1.0.0"
SCHEMA_REF = "../schemas/attack_registry.schema.json"

DISPOSITIONS = {"CLOSED", "DECOMPOSED", "SCAFFOLDED", "RED", "FALSIFIED", "REVERTED"}
CLAIM_TIERS = {"SCAFFOLD", "THEOREM", "CONJECTURE", "EXPERIMENT", "FALSIFICATION"}
BARRIER_DISPOSITIONS = {"ADDRESSED", "EXPOSED", "BLOCKED", "NOT_APPLICABLE"}
FORMAL_KINDS = {"DEFINITION", "LEMMA", "THEOREM", "BRIDGE", "PAYLOAD", "ENDPOINT", "CONSTRUCTION"}
NATIVE_VERIFIER_KINDS = {"LEAN_NATIVE", "Z3_NATIVE"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound", "native_decide"}
BASE_LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

REQUIRED_VERIFIERS = {
    "verifier.registry.strict": {
        "kind": "REGISTRY",
        "command": "python3 scripts/validate_registry.py data/attack_registry.json",
        "receipt_max_age_seconds": 0,
        "closes_claim_tiers": [],
        "requires_axiom_audit": False,
        "allowed_axioms": [],
    },
    "verifier.tests.hostile": {
        "kind": "UNIT_TEST",
        "command": "python3 -m unittest discover -s tests -v",
        "receipt_max_age_seconds": 0,
        "closes_claim_tiers": [],
        "requires_axiom_audit": False,
        "allowed_axioms": [],
    },
    "verifier.lean.native": {
        "kind": "LEAN_NATIVE",
        "command": "lake env lean Navier/AxiomAudit.lean",
        "receipt_max_age_seconds": 86400,
        "closes_claim_tiers": ["THEOREM"],
        "requires_axiom_audit": True,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound", "native_decide"],
    },
    "verifier.experiment.replay": {
        "kind": "EXPERIMENT_REPLAY",
        "command": "python3 scripts/replay_experiment.py artifacts/runs/experiment.json",
        "receipt_max_age_seconds": 86400,
        "closes_claim_tiers": ["EXPERIMENT", "FALSIFICATION"],
        "requires_axiom_audit": False,
        "allowed_axioms": [],
    },
}

REQUIRED_APPROACH_IDS = {
    "approach.exact_semantics_local_theory",
    "approach.energy",
    "approach.critical_norms",
    "approach.epsilon_regularity",
    "approach.concentration_compactness_rigidity",
    "approach.frequency_cascade",
    "approach.vorticity_geometry",
    "approach.computer_assisted_falsification",
    "approach.breakdown_construction",
}

REQUIRED_BARRIER_IDS = {
    "barrier.endpoint_semantics",
    "barrier.scaling_criticality",
    "barrier.supercritical_energy_gap",
    "barrier.compactness_defect",
    "barrier.nonlocal_pressure",
    "barrier.weak_strong_gap",
    "barrier.numerical_nonproof",
    "barrier.endpoint_circularity",
}

TOP_KEYS = {
    "$schema",
    "schema_version",
    "registry_version",
    "registry_id",
    "base_revision",
    "generated_at",
    "ssot",
    "campaign",
    "barriers",
    "references",
    "approaches",
    "verifiers",
    "evidence",
    "obligations",
}

# These hashes anchor the scientific identity of every canonical obligation in
# verifier-owned code.  The fingerprint covers its approach, formal kind,
# epistemic tier, statement, declared Lean realization, and exact PDE domain.
# Endpoint realization declarations are normalized to null here because their
# proof term is checked separately against the public branch target.  Changing
# a contract therefore requires an explicit validator change; editing registry
# data alone can never retag an open conjecture or substitute an unrelated
# theorem and then claim closure.
PINNED_OBLIGATION_CONTRACTS = {
    "semantics.encoding_bridges": "e0e3ebe52fc6b6ab29507840a2c321fe869178b88ad898e2dc3d79dcd2304a27",
    "semantics.exact_a_surface": "96fd0506fb5553297022caab783705d53a89a0bbb1956bad4d2f287761c3c647",
    "scaling.algebraic_critical_line": "f2bad6b87ea0ef6f1bb5722291e4da9abf70f4619004edb0ca9c20838231e57c",
    "local.mild_solution": "a6ea5d0c6894baac8a3dbcc42fca2e5fbe1df82cf8fc9aaf095f22637dee6e1d",
    "local.continuation_alternative": "df558110a00170a1130d036bbbd833f949dda62136ef7d7ad97fbf9989868bf5",
    "energy.smooth_identity": "7600a0c25cc75347220411696835e62c3728691b8bd70fbd7b9a2bf024b9dbfa",
    "energy.global_weak_solution": "ec003aa956dc5f8e68c3ea00f8f4211b8f9d2c629a90c5b16ba0c10c0b71bfc4",
    "energy.weak_to_strong_upgrade": "34d402552e71e8e9d2ca42ff067e8582a09e447715edac63eea32ba4bfb163a4",
    "critical.unconditional_bound": "74621c54dfbc30040b4b08e9cf75ab9106a1e15fc94d4d658a6d9cc087e16b10",
    "critical.global_regularity_bridge": "26269b9f9e935c6d83d8faed9b9256127647ec3d50785a927b38f6d02d7b1408",
    "epsilon.local_regular_criterion": "cdf6daa8485c31b4f01e3889c66722f465c8d7ecfab7e637ce8b08801b1d8864",
    "epsilon.global_singularity_exclusion": "80843c55f9115b0e5f4934569c18a633a9848110f52b21ec72d204963fba3513",
    "compact.profile_decomposition": "ada9c27caa07a307c509f7603b3a51a089556c06205bcecac5c5733b613ae9bb",
    "compact.rigidity_exclusion": "e571464255941f76b9419440b7039c1cadd5e9392c5227150b0e2fab7d955afd",
    "frequency.cascade_exclusion": "35aa9c1c5a29dab950af7bc7f69c1df948204cd30f42eb4a0f132146308611fa",
    "vorticity.alignment_criterion": "c116898d41834e21a88a9184de8c83546b596b418930493f93cf6155c808957b",
    "vorticity.unconditional_depletion": "92a4bb86b12bfe196621df6a8ee623a34991f28fbb5911e3a29a0fea936da836",
    "regularity.any_positive_route": "02aa8c4621a7a06b28dcb9d971312892907b0ade94f6cf29dc3159659ad74b69",
    "local.global_continuation": "a6121361a690e0808bdca9ed4553fbb382c8a82f245869636cada1f57e962a97",
    "endpoint.fefferman_a": "5421aa4e446b848c82243fde56462a4ec191c3eb5625dddc3ad8a9080a571bbb",
    "breakdown.exact_c_surface": "0276fa7d922166b2bc2396d2718f6a77c31ca3a611812f43ffd90df9444f9f0a",
    "breakdown.forced_c_payload": "634f8cbe6a46cbfd9f0ca115ea533539fd236a4276c7710a41bb8367e9eee671",
    "breakdown.zero_force_blowup_payload": "dee5f9eb35f869e47aa96bd176f0df3503c1fb3ee44cd4cecf02e41f90d40f02",
    "breakdown.any_exact_realization": "7acf25a847697c94b1328b9a63c840c78e37bf8937c6758c70663d61f0ea7501",
    "endpoint.fefferman_c": "6f393663090a1c0929a9316638b313e06331d8488922340405119a2f65dd82a3",
    "computation.intermediate_falsification": "b0e39cbec4f8f1455cff2f4ab93f3637d8ec795b11152a4c18b6ebc1a8964a4e",
    "breakdown.averaged_model_warning": "cc9bc79a7b36e6a1bcc895ba44503d1c621c799274fab9b6900abee5e6a5df68",
    "meta.route_triage": "f95d5afd82131d66779dda66017313ebd2ff98bcf0d8e0404a4b0d3e8b3c9ad9",
}

# Internal formal nodes are not closable merely because some Lean theorem can
# be found.  Their exact realization declaration must be pinned here first.
# Public endpoints use their separately pinned StatementA/StatementC targets.
PINNED_INTERNAL_REALIZATIONS = {
    "scaling.algebraic_critical_line": "Navier.Scaling.mixedNormExponent_eq_zero_iff",
}


@dataclass(frozen=True)
class ValidationResult:
    """The complete fail-closed validation result."""

    errors: tuple[str, ...]

    @property
    def valid(self) -> bool:
        return not self.errors


class RegistryValidationError(ValueError):
    """Raised when any registry invariant fails."""

    def __init__(self, errors: Iterable[str]) -> None:
        self.errors = tuple(errors)
        super().__init__("\n".join(self.errors))


@dataclass(frozen=True)
class NativeCheckResult:
    """Fresh trusted-kernel result for one declaration and optional target."""

    exit_code: int
    axioms: tuple[str, ...]
    artifact_sha256: str
    output: str


def load_json(path: str | Path) -> Any:
    """Load JSON without accepting duplicate object keys."""

    source = Path(path)

    def no_duplicates(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"duplicate JSON key {key!r} in {source}")
            result[key] = value
        return result

    with source.open("r", encoding="utf-8") as handle:
        return json.load(handle, object_pairs_hook=no_duplicates)


def _git_result(repo_root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        text=True,
        capture_output=True,
        check=False,
        timeout=10,
    )


def _run_native_claim_check(
    repo_root: Path,
    declaration: str,
    target: str | None,
) -> NativeCheckResult:
    """Compile a generated type check and parse its raw axiom trace.

    The generated file lives outside the repository and imports the committed
    project.  For an endpoint, the explicit type ascription proves that the
    realization declaration inhabits the public target; merely printing the
    axioms of the target proposition is therefore insufficient.
    """

    name_pattern = r"Navier(?:\.[A-Za-z][A-Za-z0-9_]*)+"
    if not re.fullmatch(name_pattern, declaration):
        return NativeCheckResult(2, (), "", "invalid realization declaration")
    if target is not None and not re.fullmatch(name_pattern, target):
        return NativeCheckResult(2, (), "", "invalid target declaration")

    lines = ["import Navier", "", f"#check {declaration}"]
    if target is not None:
        lines.append(f"#check ({declaration} : {target})")
    lines.append(f"#print axioms {declaration}")
    source = "\n".join(lines) + "\n"
    with tempfile.TemporaryDirectory(prefix="navier-native-check-") as directory:
        check_path = Path(directory) / "NativeClaimCheck.lean"
        check_path.write_text(source, encoding="utf-8")
        try:
            completed = subprocess.run(
                ["lake", "env", "lean", str(check_path)],
                cwd=repo_root,
                text=True,
                capture_output=True,
                check=False,
                timeout=300,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            text = f"native verifier failed to execute: {error}"
            return NativeCheckResult(2, (), hashlib.sha256(text.encode()).hexdigest(), text)

    output = completed.stdout + "\n-- STDERR --\n" + completed.stderr
    escaped = re.escape(declaration)
    depends = re.search(rf"'{escaped}' depends on axioms: \[([^\]]*)\]", output)
    none = re.search(rf"'{escaped}' does not depend on any axioms", output)
    if depends:
        axioms = tuple(part.strip() for part in depends.group(1).split(",") if part.strip())
    elif none:
        axioms = ()
    else:
        axioms = ()
        if completed.returncode == 0:
            completed = subprocess.CompletedProcess(completed.args, 2, completed.stdout, completed.stderr)
            output += "\nmissing raw #print axioms trace"
    digest = hashlib.sha256(output.encode("utf-8")).hexdigest()
    return NativeCheckResult(completed.returncode, axioms, digest, output)


def _obligation_contract_digest(node: dict[str, Any]) -> str:
    """Hash the immutable scientific/formal identity of one obligation."""

    declaration = node.get("formal_declaration")
    if node.get("kind") == "ENDPOINT":
        declaration = None
    payload = {
        "approach_id": node.get("approach_id"),
        "kind": node.get("kind"),
        "claim_tier": node.get("claim_tier"),
        "statement": node.get("statement"),
        "formal_declaration": declaration,
        "domain": node.get("domain"),
    }
    serialized = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=True,
    ).encode("utf-8")
    return hashlib.sha256(serialized).hexdigest()


def _validate_pinned_obligation_contracts(
    nodes: dict[str, dict[str, Any]],
    errors: list[str],
) -> None:
    """Reject data-only drift in every known scientific obligation."""

    for node_id, node in nodes.items():
        expected = PINNED_OBLIGATION_CONTRACTS.get(node_id)
        if expected is None:
            continue
        actual = _obligation_contract_digest(node)
        if actual != expected:
            errors.append(
                f"$.obligations[{node_id}]: immutable semantic/formal contract mismatch"
            )


def _exact_object(
    value: Any,
    path: str,
    keys: set[str],
    errors: list[str],
) -> dict[str, Any] | None:
    if not isinstance(value, dict):
        errors.append(f"{path}: expected object")
        return None
    actual = set(value)
    missing = sorted(keys - actual)
    unknown = sorted(actual - keys)
    if missing:
        errors.append(f"{path}: missing fields {missing}")
    if unknown:
        errors.append(f"{path}: unknown fields {unknown}")
    return value


def _list(value: Any, path: str, errors: list[str], *, nonempty: bool = False) -> list[Any]:
    if not isinstance(value, list):
        errors.append(f"{path}: expected array")
        return []
    if nonempty and not value:
        errors.append(f"{path}: must not be empty")
    return value


def _string(value: Any, path: str, errors: list[str], *, minimum: int = 1) -> str:
    if not isinstance(value, str):
        errors.append(f"{path}: expected string")
        return ""
    if len(value.strip()) < minimum:
        errors.append(f"{path}: text is too short")
    return value


_VACUOUS = re.compile(
    r"^\s*(?:true|⊤|trivial|todo|tbd|unknown|placeholder|none|punit|unit|zero)\s*[.!]?\s*$",
    re.IGNORECASE,
)


def _nonvacuous(value: Any, path: str, errors: list[str]) -> str:
    text = _string(value, path, errors, minimum=12)
    if text and _VACUOUS.fullmatch(text):
        errors.append(f"{path}: vacuous text is forbidden")
    lowered = text.casefold()
    banned_phrases = (
        "assume the clay endpoint",
        "assume the endpoint conclusion",
        "result as hypothesis",
        "wrapper around the desired result",
        "same statement as the parent",
    )
    if any(phrase in lowered for phrase in banned_phrases):
        errors.append(f"{path}: endpoint/wrapper laundering phrase is forbidden")
    return text


def _enum(value: Any, path: str, allowed: set[str], errors: list[str]) -> str:
    if not isinstance(value, str) or value not in allowed:
        errors.append(f"{path}: expected one of {sorted(allowed)}, got {value!r}")
        return ""
    return value


def _identifier(value: Any, path: str, errors: list[str]) -> str:
    text = _string(value, path, errors)
    if text and not re.fullmatch(r"[a-z][a-z0-9]*(?:[._-][a-z0-9]+)+", text):
        errors.append(f"{path}: invalid stable identifier {text!r}")
    return text


def _timestamp(value: Any, path: str, errors: list[str]) -> datetime | None:
    text = _string(value, path, errors)
    if not text:
        return None
    try:
        parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
    except ValueError:
        errors.append(f"{path}: invalid ISO-8601 timestamp")
        return None
    if parsed.tzinfo is None:
        errors.append(f"{path}: timestamp must include a timezone")
        return None
    return parsed.astimezone(UTC)


def _unique_ids(items: list[Any], path: str, errors: list[str]) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    for index, item in enumerate(items):
        if not isinstance(item, dict):
            continue
        item_id = item.get("id")
        if not isinstance(item_id, str):
            continue
        if item_id in result:
            errors.append(f"{path}[{index}].id: duplicate identifier {item_id!r}")
        else:
            result[item_id] = item
    return result


def _check_unique_strings(values: list[Any], path: str, errors: list[str]) -> list[str]:
    strings: list[str] = []
    for index, value in enumerate(values):
        if isinstance(value, str):
            strings.append(value)
        else:
            errors.append(f"{path}[{index}]: expected string")
    duplicates = sorted(key for key, count in Counter(strings).items() if count > 1)
    if duplicates:
        errors.append(f"{path}: duplicate values {duplicates}")
    return strings


def _validate_campaign(data: Any, errors: list[str]) -> dict[str, Any]:
    keys = {
        "id",
        "title",
        "summary",
        "global_disposition",
        "scientific_status",
        "problem_surface",
        "resolution_mode",
        "resolution_obligation_ids",
    }
    campaign = _exact_object(data, "$.campaign", keys, errors) or {}
    _identifier(campaign.get("id"), "$.campaign.id", errors)
    _nonvacuous(campaign.get("title"), "$.campaign.title", errors)
    _nonvacuous(campaign.get("summary"), "$.campaign.summary", errors)
    _enum(campaign.get("global_disposition"), "$.campaign.global_disposition", DISPOSITIONS, errors)
    _enum(
        campaign.get("scientific_status"),
        "$.campaign.scientific_status",
        {"SCIENTIFIC_FRONTIER", "CONDITIONAL_FRONTIER", "FORMALLY_RESOLVED"},
        errors,
    )
    if campaign.get("resolution_mode") != "ANY":
        errors.append("$.campaign.resolution_mode: Clay resolution branches must use ANY")
    resolution_ids = _check_unique_strings(
        _list(campaign.get("resolution_obligation_ids"), "$.campaign.resolution_obligation_ids", errors, nonempty=True),
        "$.campaign.resolution_obligation_ids",
        errors,
    )
    if len(resolution_ids) != 2:
        errors.append("$.campaign.resolution_obligation_ids: exactly Fefferman A and C are required")

    surface_keys = {
        "equation",
        "dimension",
        "geometry",
        "boundary",
        "viscosity",
        "viscosity_quantifier",
        "initial_data",
        "formal_path",
        "primary_branch",
        "resolution_branches",
    }
    surface = _exact_object(campaign.get("problem_surface"), "$.campaign.problem_surface", surface_keys, errors) or {}
    constants = {
        "equation": "INCOMPRESSIBLE_NAVIER_STOKES",
        "dimension": 3,
        "geometry": "R3",
        "boundary": "NONE",
        "viscosity": "POSITIVE",
        "viscosity_quantifier": "FOR_EVERY_FIXED_POSITIVE",
        "initial_data": "SMOOTH_DIVERGENCE_FREE_RAPID_DECAY",
        "formal_path": "Navier/Problem.lean",
        "primary_branch": "FEFFERMAN_A",
    }
    for field, expected in constants.items():
        if surface.get(field) != expected:
            errors.append(f"$.campaign.problem_surface.{field}: expected {expected!r}")

    branch_keys = {"id", "forcing", "target", "obligation_id", "public_declaration", "planned_formal_target"}
    branches = _list(surface.get("resolution_branches"), "$.campaign.problem_surface.resolution_branches", errors)
    by_branch: dict[str, dict[str, Any]] = {}
    for index, raw in enumerate(branches):
        path = f"$.campaign.problem_surface.resolution_branches[{index}]"
        branch = _exact_object(raw, path, branch_keys, errors) or {}
        branch_id = _enum(branch.get("id"), f"{path}.id", {"FEFFERMAN_A", "FEFFERMAN_C"}, errors)
        if branch_id in by_branch:
            errors.append(f"{path}.id: duplicate branch {branch_id!r}")
        elif branch_id:
            by_branch[branch_id] = branch
        _identifier(branch.get("obligation_id"), f"{path}.obligation_id", errors)
        for field in ("public_declaration", "planned_formal_target"):
            declaration = branch.get(field)
            if declaration is not None and (
                not isinstance(declaration, str)
                or not re.fullmatch(r"Navier(?:\.[A-Za-z][A-Za-z0-9_]*)+", declaration)
            ):
                errors.append(f"{path}.{field}: expected Lean declaration or null")

    expected_branches = {
        "FEFFERMAN_A": ("ZERO", "GLOBAL_SMOOTH_FINITE_ENERGY"),
        "FEFFERMAN_C": ("SMOOTH_RAPID_DECAY", "NO_GLOBAL_PHYSICALLY_REASONABLE_SOLUTION"),
    }
    if set(by_branch) != set(expected_branches):
        errors.append("$.campaign.problem_surface.resolution_branches: exact A/C branch pair required")
    for branch_id, (forcing, target) in expected_branches.items():
        branch = by_branch.get(branch_id, {})
        if branch and branch.get("forcing") != forcing:
            errors.append(f"$.campaign.problem_surface: {branch_id} forcing must be {forcing}")
        if branch and branch.get("target") != target:
            errors.append(f"$.campaign.problem_surface: {branch_id} target must be {target}")
        if branch and branch.get("obligation_id") not in resolution_ids:
            errors.append(f"$.campaign.problem_surface: {branch_id} obligation is not a resolution obligation")
    branch_a = by_branch.get("FEFFERMAN_A", {})
    if branch_a and (
        branch_a.get("public_declaration") != "Navier.Clay.StatementA"
        or branch_a.get("planned_formal_target") is not None
    ):
        errors.append("$.campaign.problem_surface: Fefferman A must bind the delivered Navier.Clay.StatementA")
    branch_c = by_branch.get("FEFFERMAN_C", {})
    if branch_c and (
        branch_c.get("public_declaration") is not None
        or branch_c.get("planned_formal_target") != "Navier.Clay.StatementC"
    ):
        errors.append("$.campaign.problem_surface: Fefferman C must remain an explicit planned target until delivered")
    return campaign


def _validate_references(items: Any, errors: list[str]) -> dict[str, dict[str, Any]]:
    references = _list(items, "$.references", errors, nonempty=True)
    keys = {"id", "kind", "citation", "year", "locator", "relevance"}
    for index, raw in enumerate(references):
        path = f"$.references[{index}]"
        ref = _exact_object(raw, path, keys, errors) or {}
        _identifier(ref.get("id"), f"{path}.id", errors)
        _enum(ref.get("kind"), f"{path}.kind", {"PRIMARY", "SECONDARY"}, errors)
        _nonvacuous(ref.get("citation"), f"{path}.citation", errors)
        year = ref.get("year")
        if not isinstance(year, int) or isinstance(year, bool) or not 1800 <= year <= 2100:
            errors.append(f"{path}.year: expected integer in [1800, 2100]")
        locator = _string(ref.get("locator"), f"{path}.locator", errors, minimum=8)
        if locator:
            lowered = locator.casefold()
            if any(token in lowered for token in ("/latest", "/main", "/master", "?branch=", "#head")):
                errors.append(f"{path}.locator: mutable locator is forbidden")
            stable_prefixes = ("doi:", "arxiv:", "clay:", "journal:", "isbn:")
            if not locator.startswith(stable_prefixes):
                errors.append(f"{path}.locator: expected stable DOI/arXiv/Clay/journal/ISBN locator")
            if locator.startswith("arxiv:") and not re.search(r"v[1-9][0-9]*$", locator):
                errors.append(f"{path}.locator: arXiv locators must pin a version")
        _nonvacuous(ref.get("relevance"), f"{path}.relevance", errors)
    return _unique_ids(references, "$.references", errors)


def _reference_ids(
    raw: Any,
    path: str,
    references: dict[str, dict[str, Any]],
    errors: list[str],
    *,
    require_primary: bool = True,
) -> list[str]:
    ids = _check_unique_strings(_list(raw, path, errors, nonempty=True), path, errors)
    for ref_id in ids:
        if ref_id not in references:
            errors.append(f"{path}: unknown reference {ref_id!r}")
    if require_primary and ids and not any(references.get(ref_id, {}).get("kind") == "PRIMARY" for ref_id in ids):
        errors.append(f"{path}: at least one PRIMARY reference is required")
    return ids


def _validate_barriers(
    items: Any,
    references: dict[str, dict[str, Any]],
    errors: list[str],
) -> dict[str, dict[str, Any]]:
    barriers = _list(items, "$.barriers", errors, nonempty=True)
    keys = {"id", "title", "description", "primary_reference_ids"}
    for index, raw in enumerate(barriers):
        path = f"$.barriers[{index}]"
        barrier = _exact_object(raw, path, keys, errors) or {}
        _identifier(barrier.get("id"), f"{path}.id", errors)
        _nonvacuous(barrier.get("title"), f"{path}.title", errors)
        _nonvacuous(barrier.get("description"), f"{path}.description", errors)
        _reference_ids(barrier.get("primary_reference_ids"), f"{path}.primary_reference_ids", references, errors)
    by_id = _unique_ids(barriers, "$.barriers", errors)
    if set(by_id) != REQUIRED_BARRIER_IDS:
        errors.append(
            "$.barriers: canonical barrier set mismatch; "
            f"missing={sorted(REQUIRED_BARRIER_IDS - set(by_id))}, extra={sorted(set(by_id) - REQUIRED_BARRIER_IDS)}"
        )
    return by_id


def _validate_approaches(
    items: Any,
    references: dict[str, dict[str, Any]],
    barriers: dict[str, dict[str, Any]],
    errors: list[str],
) -> dict[str, dict[str, Any]]:
    approaches = _list(items, "$.approaches", errors, nonempty=True)
    keys = {"id", "title", "objective", "status", "transfer_mechanism", "primary_reference_ids", "barrier_reviews"}
    review_keys = {"barrier_id", "disposition", "rationale", "reference_ids"}
    mechanisms = {
        "DIRECT_THEOREM_APPLICATION",
        "MAP",
        "EQUIVALENCE",
        "FUNCTORIAL_TRANSPORT",
        "QUOTIENT_LOCALIZATION",
        "COMPLETION_LIMIT",
        "REALIZATION_PAYLOAD",
        "COMPUTATION_ONLY",
        "CONSTRUCTION",
        "NONE",
    }
    for index, raw in enumerate(approaches):
        path = f"$.approaches[{index}]"
        approach = _exact_object(raw, path, keys, errors) or {}
        _identifier(approach.get("id"), f"{path}.id", errors)
        _nonvacuous(approach.get("title"), f"{path}.title", errors)
        _nonvacuous(approach.get("objective"), f"{path}.objective", errors)
        _enum(approach.get("status"), f"{path}.status", DISPOSITIONS, errors)
        _enum(approach.get("transfer_mechanism"), f"{path}.transfer_mechanism", mechanisms, errors)
        _reference_ids(approach.get("primary_reference_ids"), f"{path}.primary_reference_ids", references, errors)
        reviews = _list(approach.get("barrier_reviews"), f"{path}.barrier_reviews", errors, nonempty=True)
        seen: set[str] = set()
        for review_index, review_raw in enumerate(reviews):
            review_path = f"{path}.barrier_reviews[{review_index}]"
            review = _exact_object(review_raw, review_path, review_keys, errors) or {}
            barrier_id = _identifier(review.get("barrier_id"), f"{review_path}.barrier_id", errors)
            if barrier_id in seen:
                errors.append(f"{review_path}.barrier_id: duplicate review {barrier_id!r}")
            seen.add(barrier_id)
            if barrier_id and barrier_id not in barriers:
                errors.append(f"{review_path}.barrier_id: unknown barrier {barrier_id!r}")
            _enum(review.get("disposition"), f"{review_path}.disposition", BARRIER_DISPOSITIONS, errors)
            _nonvacuous(review.get("rationale"), f"{review_path}.rationale", errors)
            _reference_ids(review.get("reference_ids"), f"{review_path}.reference_ids", references, errors)
        if seen != set(barriers):
            errors.append(
                f"{path}.barrier_reviews: must review every canonical barrier; "
                f"missing={sorted(set(barriers) - seen)}, extra={sorted(seen - set(barriers))}"
            )
    by_id = _unique_ids(approaches, "$.approaches", errors)
    if set(by_id) != REQUIRED_APPROACH_IDS:
        errors.append(
            "$.approaches: canonical attack lanes mismatch; "
            f"missing={sorted(REQUIRED_APPROACH_IDS - set(by_id))}, extra={sorted(set(by_id) - REQUIRED_APPROACH_IDS)}"
        )
    return by_id


def _validate_verifiers(items: Any, errors: list[str]) -> dict[str, dict[str, Any]]:
    verifiers = _list(items, "$.verifiers", errors, nonempty=True)
    keys = {
        "id",
        "kind",
        "command",
        "receipt_max_age_seconds",
        "closes_claim_tiers",
        "requires_axiom_audit",
        "allowed_axioms",
    }
    kinds = {"REGISTRY", "UNIT_TEST", "LEAN_NATIVE", "Z3_NATIVE", "EXPERIMENT_REPLAY"}
    for index, raw in enumerate(verifiers):
        path = f"$.verifiers[{index}]"
        verifier = _exact_object(raw, path, keys, errors) or {}
        _identifier(verifier.get("id"), f"{path}.id", errors)
        kind = _enum(verifier.get("kind"), f"{path}.kind", kinds, errors)
        command = _string(verifier.get("command"), f"{path}.command", errors, minimum=8)
        age = verifier.get("receipt_max_age_seconds")
        if not isinstance(age, int) or isinstance(age, bool) or age < 0:
            errors.append(f"{path}.receipt_max_age_seconds: expected nonnegative integer")
        tiers = _check_unique_strings(_list(verifier.get("closes_claim_tiers"), f"{path}.closes_claim_tiers", errors), f"{path}.closes_claim_tiers", errors)
        for tier in tiers:
            _enum(tier, f"{path}.closes_claim_tiers", CLAIM_TIERS, errors)
        audit = verifier.get("requires_axiom_audit")
        if not isinstance(audit, bool):
            errors.append(f"{path}.requires_axiom_audit: expected boolean")
        axioms = set(_check_unique_strings(_list(verifier.get("allowed_axioms"), f"{path}.allowed_axioms", errors), f"{path}.allowed_axioms", errors))
        if not axioms <= ALLOWED_AXIOMS:
            errors.append(f"{path}.allowed_axioms: unsupported axioms {sorted(axioms - ALLOWED_AXIOMS)}")
        if kind == "LEAN_NATIVE":
            if "lake env lean" not in command:
                errors.append(f"{path}.command: LEAN_NATIVE must invoke `lake env lean`")
            if audit is not True:
                errors.append(f"{path}: LEAN_NATIVE requires an axiom audit")
            if not {"THEOREM", "SCAFFOLD"} & set(tiers):
                errors.append(f"{path}: LEAN_NATIVE must close a formal claim tier")
            if not BASE_LEAN_AXIOMS <= axioms:
                errors.append(f"{path}.allowed_axioms: LEAN_NATIVE allowed axioms must include the base kernel policy")
        elif kind == "Z3_NATIVE":
            if audit is not False:
                errors.append(f"{path}: Z3_NATIVE does not use a Lean axiom audit")
        elif kind == "EXPERIMENT_REPLAY":
            if set(tiers) - {"EXPERIMENT", "FALSIFICATION"}:
                errors.append(f"{path}: experiment replay cannot close formal tiers")
        elif tiers:
            errors.append(f"{path}: registry/unit-test verifiers cannot close claim tiers")
    by_id = _unique_ids(verifiers, "$.verifiers", errors)
    if set(by_id) != set(REQUIRED_VERIFIERS):
        errors.append(
            "$.verifiers: canonical verifier contract mismatch; "
            f"missing={sorted(set(REQUIRED_VERIFIERS) - set(by_id))}, "
            f"extra={sorted(set(by_id) - set(REQUIRED_VERIFIERS))}"
        )
    for verifier_id, expected in REQUIRED_VERIFIERS.items():
        actual = by_id.get(verifier_id)
        if actual is None:
            continue
        drift = {
            field: (actual.get(field), value)
            for field, value in expected.items()
            if actual.get(field) != value
        }
        if drift:
            errors.append(f"$.verifiers[{verifier_id}]: canonical verifier contract mismatch: {drift}")
    return by_id


def _validate_provenance(value: Any, path: str, errors: list[str]) -> dict[str, Any]:
    keys = {"source_locator", "source_revision", "immutable", "observed_at", "artifact_sha256"}
    provenance = _exact_object(value, path, keys, errors) or {}
    _string(provenance.get("source_locator"), f"{path}.source_locator", errors, minimum=5)
    revision = _string(provenance.get("source_revision"), f"{path}.source_revision", errors, minimum=4)
    lowered = revision.casefold()
    if any(token in lowered for token in ("head", "latest", "working-tree", "branch:", "refs/heads/", " main", "master")):
        errors.append(f"{path}.source_revision: mutable provenance is forbidden")
    if provenance.get("immutable") is not True:
        errors.append(f"{path}.immutable: evidence provenance must be immutable")
    _timestamp(provenance.get("observed_at"), f"{path}.observed_at", errors)
    digest = provenance.get("artifact_sha256")
    if digest is not None and (not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest)):
        errors.append(f"{path}.artifact_sha256: expected lowercase SHA-256 or null")
    return provenance


def _validate_receipt_shape(value: Any, path: str, errors: list[str]) -> dict[str, Any]:
    keys = {
        "verifier_id",
        "command",
        "exit_code",
        "result",
        "generated_at",
        "repository_revision",
        "declaration",
        "axioms",
        "artifact_sha256",
    }
    receipt = _exact_object(value, path, keys, errors) or {}
    _identifier(receipt.get("verifier_id"), f"{path}.verifier_id", errors)
    _string(receipt.get("command"), f"{path}.command", errors, minimum=8)
    if not isinstance(receipt.get("exit_code"), int) or isinstance(receipt.get("exit_code"), bool):
        errors.append(f"{path}.exit_code: expected integer")
    _enum(receipt.get("result"), f"{path}.result", {"PASS", "FAIL"}, errors)
    _timestamp(receipt.get("generated_at"), f"{path}.generated_at", errors)
    revision = receipt.get("repository_revision")
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        errors.append(f"{path}.repository_revision: expected immutable 40-character Git revision")
    declaration = receipt.get("declaration")
    if declaration is not None and (not isinstance(declaration, str) or len(declaration) < 3):
        errors.append(f"{path}.declaration: expected declaration string or null")
    _check_unique_strings(_list(receipt.get("axioms"), f"{path}.axioms", errors), f"{path}.axioms", errors)
    digest = receipt.get("artifact_sha256")
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        errors.append(f"{path}.artifact_sha256: expected lowercase SHA-256")
    return receipt


def _validate_evidence(
    items: Any,
    references: dict[str, dict[str, Any]],
    verifiers: dict[str, dict[str, Any]],
    base_revision: str,
    now: datetime,
    repo_root: Path | None,
    check_git_revision: bool,
    errors: list[str],
) -> dict[str, dict[str, Any]]:
    evidence_items = _list(items, "$.evidence", errors)
    keys = {"id", "kind", "claim_tier", "summary", "reference_ids", "supports", "provenance", "receipt"}
    kinds = {
        "PRIMARY_REFERENCE_EVIDENCE",
        "NATIVE_RECEIPT",
        "EXPERIMENT_RECEIPT",
        "FALSIFICATION_WITNESS",
        "FORMAL_SURFACE_SNAPSHOT",
    }
    tiers = {"REFERENCE", "THEOREM", "EXPERIMENT", "FALSIFICATION", "SCAFFOLD"}
    for index, raw in enumerate(evidence_items):
        path = f"$.evidence[{index}]"
        evidence = _exact_object(raw, path, keys, errors) or {}
        _identifier(evidence.get("id"), f"{path}.id", errors)
        kind = _enum(evidence.get("kind"), f"{path}.kind", kinds, errors)
        tier = _enum(evidence.get("claim_tier"), f"{path}.claim_tier", tiers, errors)
        allowed_tiers = {
            "PRIMARY_REFERENCE_EVIDENCE": {"REFERENCE"},
            "NATIVE_RECEIPT": {"THEOREM", "SCAFFOLD"},
            "EXPERIMENT_RECEIPT": {"EXPERIMENT", "FALSIFICATION"},
            "FALSIFICATION_WITNESS": {"FALSIFICATION"},
            "FORMAL_SURFACE_SNAPSHOT": {"SCAFFOLD"},
        }
        if kind and tier not in allowed_tiers.get(kind, set()):
            errors.append(f"{path}.claim_tier: incompatible with evidence kind {kind}")
        _nonvacuous(evidence.get("summary"), f"{path}.summary", errors)
        reference_ids = _reference_ids(
            evidence.get("reference_ids"),
            f"{path}.reference_ids",
            references,
            errors,
        )
        _check_unique_strings(_list(evidence.get("supports"), f"{path}.supports", errors, nonempty=True), f"{path}.supports", errors)
        provenance = _validate_provenance(evidence.get("provenance"), f"{path}.provenance", errors)
        if kind == "PRIMARY_REFERENCE_EVIDENCE":
            if len(reference_ids) != 1:
                errors.append(
                    f"{path}.reference_ids: primary evidence requires exactly one source-specific provenance record"
                )
            elif references.get(reference_ids[0], {}).get("locator") != provenance.get("source_locator"):
                errors.append(
                    f"{path}.provenance.source_locator: must equal the referenced primary source locator"
                )
        receipt_raw = evidence.get("receipt")
        receipt: dict[str, Any] | None = None
        if receipt_raw is not None:
            receipt = _validate_receipt_shape(receipt_raw, f"{path}.receipt", errors)
        if kind in {"NATIVE_RECEIPT", "EXPERIMENT_RECEIPT"} and receipt is None:
            errors.append(f"{path}.receipt: receipt evidence must include a receipt")
        if kind not in {"NATIVE_RECEIPT", "EXPERIMENT_RECEIPT"} and receipt is not None:
            errors.append(f"{path}.receipt: only receipt evidence may carry a receipt")
        if kind in {
            "NATIVE_RECEIPT",
            "EXPERIMENT_RECEIPT",
            "FALSIFICATION_WITNESS",
            "FORMAL_SURFACE_SNAPSHOT",
        } and not provenance.get("artifact_sha256"):
            errors.append(f"{path}.provenance.artifact_sha256: artifact-backed evidence requires a digest")
        if receipt is not None:
            verifier = verifiers.get(receipt.get("verifier_id"))
            if verifier is None:
                errors.append(f"{path}.receipt.verifier_id: unknown verifier {receipt.get('verifier_id')!r}")
            else:
                if receipt.get("command") != verifier.get("command"):
                    errors.append(f"{path}.receipt.command: command does not match registered verifier")
                generated = _timestamp(receipt.get("generated_at"), f"{path}.receipt.generated_at", errors)
                max_age = verifier.get("receipt_max_age_seconds")
                if generated is not None and isinstance(max_age, int):
                    age = (now - generated).total_seconds()
                    if age < -300:
                        errors.append(f"{path}.receipt.generated_at: receipt is from the future")
                    elif age > max_age:
                        errors.append(f"{path}.receipt.generated_at: stale receipt ({int(age)}s > {max_age}s)")
                if kind == "NATIVE_RECEIPT" and verifier.get("kind") not in NATIVE_VERIFIER_KINDS:
                    errors.append(f"{path}: native receipt uses a non-native verifier")
                if kind == "EXPERIMENT_RECEIPT" and verifier.get("kind") != "EXPERIMENT_REPLAY":
                    errors.append(f"{path}: experiment receipt uses a non-experiment verifier")
            receipt_revision = receipt.get("repository_revision")
            if provenance.get("source_revision") != receipt_revision:
                errors.append(
                    f"{path}.receipt.repository_revision: receipt revision must match immutable provenance source revision"
                )
            if (
                check_git_revision
                and repo_root is not None
                and isinstance(receipt_revision, str)
                and re.fullmatch(r"[0-9a-f]{40}", receipt_revision)
            ):
                exists = _git_result(repo_root, "cat-file", "-e", f"{receipt_revision}^{{commit}}")
                if exists.returncode != 0:
                    errors.append(f"{path}.receipt.repository_revision: missing or unverifiable receipt commit")
                else:
                    after_baseline = _git_result(
                        repo_root, "merge-base", "--is-ancestor", base_revision, receipt_revision
                    )
                    before_head = _git_result(
                        repo_root, "merge-base", "--is-ancestor", receipt_revision, "HEAD"
                    )
                    if after_baseline.returncode != 0:
                        errors.append(f"{path}.receipt.repository_revision: receipt predates the campaign baseline")
                    if before_head.returncode != 0:
                        errors.append(f"{path}.receipt.repository_revision: receipt commit is not an ancestor of HEAD")
            if receipt.get("artifact_sha256") != provenance.get("artifact_sha256"):
                errors.append(f"{path}: receipt/provenance artifact digests differ")
    return _unique_ids(evidence_items, "$.evidence", errors)


def _validate_domain(value: Any, path: str, errors: list[str]) -> dict[str, Any]:
    keys = {
        "equation",
        "dimension",
        "geometry",
        "boundary",
        "forcing",
        "viscosity",
        "viscosity_quantifier",
        "solution_class",
        "relation_to_endpoint",
        "endpoint_branch",
    }
    domain = _exact_object(value, path, keys, errors) or {}
    _enum(domain.get("equation"), f"{path}.equation", {"INCOMPRESSIBLE_NAVIER_STOKES", "DISCRETE_NAVIER_STOKES", "AVERAGED_NAVIER_STOKES"}, errors)
    dimension = domain.get("dimension")
    if not isinstance(dimension, int) or isinstance(dimension, bool) or not 2 <= dimension <= 4:
        errors.append(f"{path}.dimension: expected integer in [2, 4]")
    _enum(domain.get("geometry"), f"{path}.geometry", {"R3", "TORUS3", "BOUNDED_DOMAIN", "DISCRETE_GRID"}, errors)
    _enum(domain.get("boundary"), f"{path}.boundary", {"NONE", "PERIODIC", "NO_SLIP", "DISCRETE"}, errors)
    _enum(domain.get("forcing"), f"{path}.forcing", {"ZERO", "SMOOTH_RAPID_DECAY", "DISCRETE"}, errors)
    _enum(domain.get("viscosity"), f"{path}.viscosity", {"POSITIVE", "ZERO", "DISCRETE_POSITIVE"}, errors)
    _enum(
        domain.get("viscosity_quantifier"),
        f"{path}.viscosity_quantifier",
        {"FOR_EVERY_FIXED_POSITIVE", "FIXED_DISCRETE_POSITIVE", "NOT_APPLICABLE"},
        errors,
    )
    _enum(
        domain.get("solution_class"),
        f"{path}.solution_class",
        {"EXACT_SMOOTH_FINITE_ENERGY", "CRITICAL_MILD", "SUITABLE_WEAK", "DISTRIBUTIONAL_WEAK", "DISCRETE_APPROXIMATION"},
        errors,
    )
    _enum(
        domain.get("relation_to_endpoint"),
        f"{path}.relation_to_endpoint",
        {"EXACT", "PREREQUISITE", "STRONGER_THAN_C", "APPROXIMATION_ONLY", "ANALOGUE_ONLY"},
        errors,
    )
    _enum(domain.get("endpoint_branch"), f"{path}.endpoint_branch", {"FEFFERMAN_A", "FEFFERMAN_C", "SHARED", "NONE"}, errors)
    return domain


def _validate_residual(value: Any, path: str, statement: str, errors: list[str]) -> dict[str, Any] | None:
    if value is None:
        return None
    keys = {"statement", "smaller_than", "consumer_ids", "falsifier", "next_action"}
    residual = _exact_object(value, path, keys, errors) or {}
    residual_statement = _nonvacuous(residual.get("statement"), f"{path}.statement", errors)
    _nonvacuous(residual.get("smaller_than"), f"{path}.smaller_than", errors)
    _check_unique_strings(_list(residual.get("consumer_ids"), f"{path}.consumer_ids", errors, nonempty=True), f"{path}.consumer_ids", errors)
    _nonvacuous(residual.get("falsifier"), f"{path}.falsifier", errors)
    _nonvacuous(residual.get("next_action"), f"{path}.next_action", errors)
    def normalize(text: str) -> str:
        return re.sub(r"\W+", "", text.casefold())

    if residual_statement and statement and normalize(residual_statement) == normalize(statement):
        errors.append(f"{path}.statement: residual merely repeats the parent obligation")
    return residual


def _validate_obligations_shape(
    items: Any,
    approaches: dict[str, dict[str, Any]],
    barriers: dict[str, dict[str, Any]],
    references: dict[str, dict[str, Any]],
    evidence: dict[str, dict[str, Any]],
    verifiers: dict[str, dict[str, Any]],
    errors: list[str],
) -> dict[str, dict[str, Any]]:
    obligations = _list(items, "$.obligations", errors, nonempty=True)
    keys = {
        "id",
        "approach_id",
        "title",
        "kind",
        "claim_tier",
        "disposition",
        "statement",
        "formal_declaration",
        "dependency_mode",
        "dependencies",
        "assumption_ids",
        "domain",
        "reference_ids",
        "evidence_links",
        "verifier_ids",
        "barrier_ids",
        "residual",
    }
    kinds = FORMAL_KINDS | {"EXPERIMENT", "FALSIFICATION", "META"}
    link_keys = {"evidence_id", "role"}
    for index, raw in enumerate(obligations):
        path = f"$.obligations[{index}]"
        node = _exact_object(raw, path, keys, errors) or {}
        _identifier(node.get("id"), f"{path}.id", errors)
        approach_id = _identifier(node.get("approach_id"), f"{path}.approach_id", errors)
        if approach_id and approach_id not in approaches:
            errors.append(f"{path}.approach_id: unknown approach {approach_id!r}")
        _nonvacuous(node.get("title"), f"{path}.title", errors)
        kind = _enum(node.get("kind"), f"{path}.kind", kinds, errors)
        tier = _enum(node.get("claim_tier"), f"{path}.claim_tier", CLAIM_TIERS, errors)
        disposition = _enum(node.get("disposition"), f"{path}.disposition", DISPOSITIONS, errors)
        statement = _nonvacuous(node.get("statement"), f"{path}.statement", errors)
        declaration = node.get("formal_declaration")
        if declaration is not None and (not isinstance(declaration, str) or len(declaration) < 3):
            errors.append(f"{path}.formal_declaration: expected string or null")
        mode = _enum(node.get("dependency_mode"), f"{path}.dependency_mode", {"ALL", "ANY", "NONE"}, errors)
        dependencies = _check_unique_strings(_list(node.get("dependencies"), f"{path}.dependencies", errors), f"{path}.dependencies", errors)
        _check_unique_strings(
            _list(node.get("assumption_ids"), f"{path}.assumption_ids", errors),
            f"{path}.assumption_ids",
            errors,
        )
        if mode == "NONE" and dependencies:
            errors.append(f"{path}: dependency_mode NONE requires no dependencies")
        if mode in {"ALL", "ANY"} and not dependencies:
            errors.append(f"{path}: dependency_mode {mode} requires dependencies")
        if mode == "ANY" and len(dependencies) < 2:
            errors.append(f"{path}: dependency_mode ANY requires at least two alternatives")
        _validate_domain(node.get("domain"), f"{path}.domain", errors)
        _reference_ids(node.get("reference_ids"), f"{path}.reference_ids", references, errors)
        links = _list(node.get("evidence_links"), f"{path}.evidence_links", errors)
        seen_links: set[str] = set()
        for link_index, link_raw in enumerate(links):
            link_path = f"{path}.evidence_links[{link_index}]"
            link = _exact_object(link_raw, link_path, link_keys, errors) or {}
            evidence_id = _identifier(link.get("evidence_id"), f"{link_path}.evidence_id", errors)
            role = _enum(link.get("role"), f"{link_path}.role", {"BACKGROUND", "OBSERVATION", "REALIZATION", "FALSIFICATION"}, errors)
            if evidence_id in seen_links:
                errors.append(f"{link_path}.evidence_id: duplicate evidence link {evidence_id!r}")
            seen_links.add(evidence_id)
            evidence_item = evidence.get(evidence_id)
            if evidence_item is None and evidence_id:
                errors.append(f"{link_path}.evidence_id: unknown evidence {evidence_id!r}")
            elif evidence_item is not None:
                if node.get("id") not in evidence_item.get("supports", []):
                    errors.append(f"{link_path}: evidence does not declare support for this obligation")
                if evidence_item.get("kind") == "EXPERIMENT_RECEIPT" and role not in {"OBSERVATION", "FALSIFICATION"}:
                    errors.append(f"{link_path}: experiment-as-proof laundering is forbidden")
            if tier == "EXPERIMENT" and role == "REALIZATION":
                errors.append(f"{link_path}: an experiment cannot realize a formal claim")
        verifier_ids = _check_unique_strings(_list(node.get("verifier_ids"), f"{path}.verifier_ids", errors, nonempty=True), f"{path}.verifier_ids", errors)
        for verifier_id in verifier_ids:
            if verifier_id not in verifiers:
                errors.append(f"{path}.verifier_ids: unknown verifier {verifier_id!r}")
        barrier_ids = _check_unique_strings(_list(node.get("barrier_ids"), f"{path}.barrier_ids", errors, nonempty=True), f"{path}.barrier_ids", errors)
        for barrier_id in barrier_ids:
            if barrier_id not in barriers:
                errors.append(f"{path}.barrier_ids: unknown barrier {barrier_id!r}")
        residual = _validate_residual(node.get("residual"), f"{path}.residual", statement, errors)
        if disposition in {"CLOSED", "FALSIFIED", "REVERTED"}:
            if residual is not None:
                errors.append(f"{path}.residual: verified dispositions must not carry an open residual")
        elif residual is None:
            errors.append(f"{path}.residual: open dispositions require a non-vacuous residual")
        if kind == "EXPERIMENT" and tier != "EXPERIMENT":
            errors.append(f"{path}: EXPERIMENT kind requires EXPERIMENT claim tier")
        if tier == "EXPERIMENT" and kind not in {"EXPERIMENT", "FALSIFICATION"}:
            errors.append(f"{path}: EXPERIMENT tier cannot type a formal obligation")
        if kind == "FALSIFICATION" and tier != "FALSIFICATION":
            errors.append(f"{path}: FALSIFICATION kind requires FALSIFICATION claim tier")
        if disposition == "CLOSED" and kind in FORMAL_KINDS and not declaration:
            errors.append(f"{path}.formal_declaration: closed formal obligations require a declaration")
        if kind == "ENDPOINT" and tier != "THEOREM":
            errors.append(f"{path}: endpoint must be a THEOREM-tier formal target")
    return _unique_ids(obligations, "$.obligations", errors)


def _detect_cycles(nodes: dict[str, dict[str, Any]], errors: list[str]) -> None:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(node_id: str) -> None:
        marker = state.get(node_id, 0)
        if marker == 1:
            try:
                start = stack.index(node_id)
            except ValueError:
                start = 0
            cycle = stack[start:] + [node_id]
            errors.append(f"$.obligations: dependency/assumption cycle detected: {' -> '.join(cycle)}")
            return
        if marker == 2:
            return
        state[node_id] = 1
        stack.append(node_id)
        node = nodes[node_id]
        for child in node.get("dependencies", []) + node.get("assumption_ids", []):
            if child in nodes:
                visit(child)
        stack.pop()
        state[node_id] = 2

    for node_id in nodes:
        if state.get(node_id, 0) == 0:
            visit(node_id)


def _ancestors(root_id: str, nodes: dict[str, dict[str, Any]]) -> set[str]:
    seen: set[str] = set()
    pending = [root_id]
    while pending:
        node_id = pending.pop()
        if node_id in seen or node_id not in nodes:
            continue
        seen.add(node_id)
        node = nodes[node_id]
        pending.extend(node.get("dependencies", []))
        pending.extend(node.get("assumption_ids", []))
    return seen


def _validate_graph_and_epistemics(
    campaign: dict[str, Any],
    approaches: dict[str, dict[str, Any]],
    nodes: dict[str, dict[str, Any]],
    evidence: dict[str, dict[str, Any]],
    verifiers: dict[str, dict[str, Any]],
    base_revision: str,
    repo_root: Path | None,
    check_native_receipts: bool,
    errors: list[str],
) -> None:
    resolution_ids = set(campaign.get("resolution_obligation_ids", []))
    for resolution_id in resolution_ids:
        node = nodes.get(resolution_id)
        if node is None:
            errors.append(f"$.campaign.resolution_obligation_ids: unknown endpoint {resolution_id!r}")
        elif node.get("kind") != "ENDPOINT":
            errors.append(f"$.campaign.resolution_obligation_ids: {resolution_id!r} is not an ENDPOINT")
    branches = campaign.get("problem_surface", {}).get("resolution_branches", [])
    branch_by_obligation = {
        branch.get("obligation_id"): branch.get("id")
        for branch in branches
        if isinstance(branch, dict)
    }
    for endpoint_id, branch_id in branch_by_obligation.items():
        endpoint = nodes.get(endpoint_id)
        if endpoint is None:
            continue
        target_declaration = next(
            (branch.get("public_declaration") for branch in branches if branch.get("obligation_id") == endpoint_id),
            None,
        )
        realization_declaration = endpoint.get("formal_declaration")
        if endpoint.get("disposition") != "CLOSED" and realization_declaration is not None:
            errors.append(
                f"$.obligations[{endpoint_id}].formal_declaration: open endpoint cannot advertise a realization declaration"
            )
        if endpoint.get("disposition") == "CLOSED" and target_declaration is None:
            errors.append(f"$.obligations[{endpoint_id}]: planned formal target cannot support closure")
        if (
            endpoint.get("disposition") == "CLOSED"
            and realization_declaration is not None
            and realization_declaration == target_declaration
        ):
            errors.append(
                f"$.obligations[{endpoint_id}]: endpoint target definition cannot serve as its realization proof"
            )
        domain = endpoint.get("domain", {})
        if domain.get("endpoint_branch") != branch_id or domain.get("relation_to_endpoint") != "EXACT":
            errors.append(f"$.obligations[{endpoint_id}].domain: endpoint must have exact {branch_id} domain")
        expected_forcing = "ZERO" if branch_id == "FEFFERMAN_A" else "SMOOTH_RAPID_DECAY"
        if domain.get("forcing") != expected_forcing:
            errors.append(f"$.obligations[{endpoint_id}].domain.forcing: {branch_id} requires {expected_forcing}")
        if domain.get("solution_class") != "EXACT_SMOOTH_FINITE_ENERGY":
            errors.append(
                f"$.obligations[{endpoint_id}].domain.solution_class: endpoint must use EXACT_SMOOTH_FINITE_ENERGY"
            )
        if endpoint.get("assumption_ids"):
            errors.append(f"$.obligations[{endpoint_id}].assumption_ids: public endpoint cannot be assumption-backed")

    for node_id, node in nodes.items():
        for field in ("dependencies", "assumption_ids"):
            for target in node.get(field, []):
                if target not in nodes:
                    errors.append(f"$.obligations[{node_id}].{field}: unknown obligation {target!r}")
        for assumption_id in node.get("assumption_ids", []):
            if assumption_id in resolution_ids or nodes.get(assumption_id, {}).get("kind") == "ENDPOINT":
                errors.append(f"$.obligations[{node_id}].assumption_ids: endpoint-as-assumption is forbidden")
        if node.get("kind") in FORMAL_KINDS:
            for dependency_id in node.get("dependencies", []):
                dependency = nodes.get(dependency_id, {})
                if dependency.get("claim_tier") == "EXPERIMENT" or dependency.get("kind") == "EXPERIMENT":
                    errors.append(
                        f"$.obligations[{node_id}].dependencies: experiment {dependency_id!r} cannot realize a formal claim"
                    )

    _detect_cycles(nodes, errors)

    for node_id, node in nodes.items():
        if node.get("kind") not in FORMAL_KINDS:
            continue
        for ancestor_id in _ancestors(node_id, nodes) - {node_id}:
            ancestor = nodes[ancestor_id]
            if ancestor.get("kind") == "EXPERIMENT" or ancestor.get("claim_tier") == "EXPERIMENT":
                errors.append(
                    f"$.obligations[{node_id}]: experiment-tainted proof path reaches {ancestor_id!r}"
                )
        if node_id in resolution_ids:
            for ancestor_id in _ancestors(node_id, nodes):
                if nodes[ancestor_id].get("kind") not in FORMAL_KINDS:
                    errors.append(
                        f"$.obligations[{ancestor_id}]: non-formal node cannot lie on a public endpoint proof path"
                    )

    consumers: dict[str, set[str]] = defaultdict(set)
    for consumer_id, node in nodes.items():
        for dependency_id in node.get("dependencies", []) + node.get("assumption_ids", []):
            consumers[dependency_id].add(consumer_id)
    campaign_consumer = f"campaign:{campaign.get('id', '')}"
    for node_id, node in nodes.items():
        residual = node.get("residual")
        if not isinstance(residual, dict):
            continue
        for consumer_id in residual.get("consumer_ids", []):
            if consumer_id == campaign_consumer:
                if node_id not in resolution_ids and node.get("kind") != "META":
                    errors.append(
                        f"$.obligations[{node_id}].residual.consumer_ids: only endpoints/meta records may feed the campaign directly"
                    )
            elif consumer_id not in nodes:
                errors.append(f"$.obligations[{node_id}].residual.consumer_ids: unknown consumer {consumer_id!r}")
            elif consumer_id not in consumers[node_id]:
                errors.append(
                    f"$.obligations[{node_id}].residual.consumer_ids: {consumer_id!r} does not consume this obligation"
                )

    exact_core = {
        "equation": "INCOMPRESSIBLE_NAVIER_STOKES",
        "dimension": 3,
        "geometry": "R3",
        "boundary": "NONE",
        "viscosity": "POSITIVE",
        "viscosity_quantifier": "FOR_EVERY_FIXED_POSITIVE",
    }
    for endpoint_id, branch_id in branch_by_obligation.items():
        for ancestor_id in _ancestors(endpoint_id, nodes):
            domain = nodes[ancestor_id].get("domain", {})
            relation = domain.get("relation_to_endpoint")
            if relation in {"APPROXIMATION_ONLY", "ANALOGUE_ONLY"}:
                errors.append(
                    f"$.obligations[{ancestor_id}].domain: wrong-domain node cannot lie on the {branch_id} proof path"
                )
            for field, expected in exact_core.items():
                if domain.get(field) != expected:
                    errors.append(
                        f"$.obligations[{ancestor_id}].domain.{field}: wrong object on {branch_id} proof path; expected {expected!r}"
                    )
            node_branch = domain.get("endpoint_branch")
            if branch_id == "FEFFERMAN_A":
                if node_branch not in {"FEFFERMAN_A", "SHARED"}:
                    errors.append(f"$.obligations[{ancestor_id}].domain: branch mismatch on Fefferman A path")
                if domain.get("forcing") != "ZERO":
                    errors.append(f"$.obligations[{ancestor_id}].domain.forcing: Fefferman A path requires ZERO")
            elif branch_id == "FEFFERMAN_C":
                if node_branch not in {"FEFFERMAN_C", "SHARED"}:
                    errors.append(f"$.obligations[{ancestor_id}].domain: branch mismatch on Fefferman C path")
                if relation == "STRONGER_THAN_C":
                    if domain.get("forcing") != "ZERO":
                        errors.append(f"$.obligations[{ancestor_id}].domain: STRONGER_THAN_C route must be explicitly ZERO force")
                elif domain.get("forcing") != "SMOOTH_RAPID_DECAY":
                    errors.append(
                        f"$.obligations[{ancestor_id}].domain.forcing: exact/prerequisite Fefferman C path requires SMOOTH_RAPID_DECAY"
                    )

    for node_id, node in nodes.items():
        disposition = node.get("disposition")
        links = node.get("evidence_links", [])
        linked = [evidence.get(link.get("evidence_id"), {}) for link in links]
        if disposition == "CLOSED" and node.get("assumption_ids"):
            errors.append(f"$.obligations[{node_id}]: CLOSED obligation cannot be assumption-backed")
        if disposition == "CLOSED" and node.get("kind") in FORMAL_KINDS:
            native = [
                item
                for link, item in zip(links, linked, strict=False)
                if link.get("role") == "REALIZATION" and item.get("kind") == "NATIVE_RECEIPT"
            ]
            if not native:
                errors.append(f"$.obligations[{node_id}]: false closure claim; fresh native receipt required")
            if len(native) > 1:
                errors.append(f"$.obligations[{node_id}]: exactly one native realization receipt is required")
            declaration = node.get("formal_declaration")
            target = None
            if node_id in branch_by_obligation:
                target = next(
                    (
                        branch.get("public_declaration")
                        for branch in branches
                        if branch.get("obligation_id") == node_id
                    ),
                    None,
                )
            else:
                pinned_realization = PINNED_INTERNAL_REALIZATIONS.get(node_id)
                if pinned_realization is None:
                    errors.append(
                        f"$.obligations[{node_id}]: internal closure has no immutable formal realization contract"
                    )
                elif declaration != pinned_realization:
                    errors.append(
                        f"$.obligations[{node_id}].formal_declaration: does not match the immutable realization contract"
                    )
            for receipt_evidence in native:
                receipt = receipt_evidence.get("receipt") or {}
                verifier = verifiers.get(receipt.get("verifier_id"), {})
                if verifier.get("kind") not in NATIVE_VERIFIER_KINDS:
                    errors.append(f"$.obligations[{node_id}]: closure receipt is not native")
                if node.get("claim_tier") not in verifier.get("closes_claim_tiers", []):
                    errors.append(f"$.obligations[{node_id}]: verifier is not authorized for this claim tier")
                if receipt.get("exit_code") != 0 or receipt.get("result") != "PASS":
                    errors.append(f"$.obligations[{node_id}]: failing receipt cannot close a claim")
                if receipt.get("declaration") != declaration:
                    errors.append(f"$.obligations[{node_id}]: receipt declaration does not match obligation")
                axioms = set(receipt.get("axioms", []))
                if verifier.get("requires_axiom_audit") and not axioms <= set(verifier.get("allowed_axioms", [])):
                    errors.append(f"$.obligations[{node_id}]: axiom audit contains forbidden dependencies")
                if not check_native_receipts or repo_root is None or not isinstance(declaration, str):
                    errors.append(f"$.obligations[{node_id}]: native receipt was not freshly revalidated")
                    continue
                receipt_revision = receipt.get("repository_revision")
                if isinstance(receipt_revision, str) and re.fullmatch(r"[0-9a-f]{40}", receipt_revision):
                    formal_paths = (
                        "Navier",
                        "Navier.lean",
                        "Main.lean",
                        "lakefile.toml",
                        "lake-manifest.json",
                        "lean-toolchain",
                    )
                    formal_diff = _git_result(
                        repo_root,
                        "diff",
                        "--quiet",
                        receipt_revision,
                        "HEAD",
                        "--",
                        *formal_paths,
                    )
                    if formal_diff.returncode != 0:
                        errors.append(
                            f"$.obligations[{node_id}]: formal sources changed after the receipt revision"
                        )
                        continue
                    worktree = _git_result(
                        repo_root,
                        "status",
                        "--porcelain=v1",
                        "--untracked-files=all",
                        "--",
                        *formal_paths,
                    )
                    if worktree.returncode != 0 or worktree.stdout.strip():
                        errors.append(
                            f"$.obligations[{node_id}]: native verification requires a clean formal worktree"
                        )
                        continue
                native_result = _run_native_claim_check(repo_root, declaration, target)
                if native_result.exit_code != 0:
                    errors.append(f"$.obligations[{node_id}]: native receipt revalidation failed")
                    continue
                actual_axioms = set(native_result.axioms)
                if actual_axioms != axioms:
                    errors.append(f"$.obligations[{node_id}]: native axiom trace does not match the receipt")
                if not actual_axioms <= set(verifier.get("allowed_axioms", [])):
                    errors.append(f"$.obligations[{node_id}]: freshly checked declaration uses forbidden axioms")
                if native_result.artifact_sha256 != receipt.get("artifact_sha256"):
                    errors.append(f"$.obligations[{node_id}]: native receipt artifact digest mismatch")
            mode = node.get("dependency_mode")
            dependency_statuses = [nodes.get(dep, {}).get("disposition") for dep in node.get("dependencies", [])]
            if mode == "ALL" and any(status != "CLOSED" for status in dependency_statuses):
                errors.append(f"$.obligations[{node_id}]: ALL-dependency closure requires every dependency CLOSED")
            if mode == "ANY" and not any(status == "CLOSED" for status in dependency_statuses):
                errors.append(f"$.obligations[{node_id}]: ANY-dependency closure requires one CLOSED branch")
        if disposition in {"FALSIFIED", "REVERTED"}:
            witnesses = [
                item
                for link, item in zip(links, linked, strict=False)
                if link.get("role") == "FALSIFICATION" and item.get("kind") == "FALSIFICATION_WITNESS"
            ]
            if not witnesses:
                errors.append(f"$.obligations[{node_id}]: falsified/reverted disposition requires a checked witness")

    closed_endpoints = [node_id for node_id in resolution_ids if nodes.get(node_id, {}).get("disposition") == "CLOSED"]
    global_closed = campaign.get("global_disposition") == "CLOSED"
    formally_resolved = campaign.get("scientific_status") == "FORMALLY_RESOLVED"
    if closed_endpoints and not (global_closed and formally_resolved):
        errors.append("$.campaign: a closed public endpoint requires CLOSED / FORMALLY_RESOLVED global status")
    if (global_closed or formally_resolved) and not closed_endpoints:
        errors.append("$.campaign: false global closure claim; no public endpoint is natively closed")
    if not closed_endpoints and (
        campaign.get("global_disposition") != "SCAFFOLDED"
        or campaign.get("scientific_status") != "SCIENTIFIC_FRONTIER"
    ):
        errors.append("$.campaign: open campaign must remain SCAFFOLDED / SCIENTIFIC_FRONTIER")

    for approach_id, approach in approaches.items():
        approach_nodes = [node for node in nodes.values() if node.get("approach_id") == approach_id]
        if approach.get("status") == "CLOSED" and (
            not approach_nodes or any(node.get("disposition") != "CLOSED" for node in approach_nodes)
        ):
            errors.append(f"$.approaches[{approach_id}]: CLOSED approach requires every obligation CLOSED")


def validate_registry(
    data: Any,
    *,
    now: datetime | None = None,
    repo_root: str | Path | None = None,
    check_git_revision: bool = True,
    check_native_receipts: bool = True,
) -> ValidationResult:
    """Validate a registry and return every detected error.

    Unknown/missing structure is never ignored.  Cross-reference checks run on
    whatever well-typed subset remains so one invocation exposes independent
    hostile defects without treating partial parsing as success.
    """

    errors: list[str] = []
    top = _exact_object(data, "$", TOP_KEYS, errors)
    if top is None:
        return ValidationResult(tuple(errors))
    if top.get("$schema") != SCHEMA_REF:
        errors.append(f"$.$schema: expected {SCHEMA_REF!r}")
    if top.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"$.schema_version: expected {SCHEMA_VERSION!r}")
    version = top.get("registry_version")
    if not isinstance(version, str) or not re.fullmatch(r"[1-9][0-9]*\.[0-9]+\.[0-9]+", version):
        errors.append("$.registry_version: expected semantic version")
    _identifier(top.get("registry_id"), "$.registry_id", errors)
    base_revision = top.get("base_revision")
    if not isinstance(base_revision, str) or not re.fullmatch(r"[0-9a-f]{40}", base_revision):
        errors.append("$.base_revision: expected immutable 40-character Git revision")
        base_revision = ""
    _timestamp(top.get("generated_at"), "$.generated_at", errors)
    if top.get("ssot") is not True:
        errors.append("$.ssot: must be true; status views are derived")

    if check_git_revision and repo_root is not None and base_revision:
        try:
            subprocess.run(
                ["git", "cat-file", "-e", f"{base_revision}^{{commit}}"],
                cwd=Path(repo_root),
                check=True,
                capture_output=True,
                text=True,
                timeout=5,
            )
            ancestor = subprocess.run(
                ["git", "merge-base", "--is-ancestor", base_revision, "HEAD"],
                cwd=Path(repo_root),
                check=False,
                capture_output=True,
                text=True,
                timeout=5,
            )
            if ancestor.returncode == 1:
                errors.append("$.base_revision: revision is not an ancestor of HEAD")
            elif ancestor.returncode != 0:
                errors.append(
                    "$.base_revision: could not compare revision with HEAD: "
                    f"{ancestor.stderr.strip() or f'exit {ancestor.returncode}'}"
                )
        except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
            errors.append(f"$.base_revision: missing or unverifiable baseline commit: {exc}")

    now_utc = (now or datetime.now(tz=UTC)).astimezone(UTC)
    campaign = _validate_campaign(top.get("campaign"), errors)
    references = _validate_references(top.get("references"), errors)
    barriers = _validate_barriers(top.get("barriers"), references, errors)
    approaches = _validate_approaches(top.get("approaches"), references, barriers, errors)
    verifiers = _validate_verifiers(top.get("verifiers"), errors)
    root_path = Path(repo_root).resolve() if repo_root is not None else None
    if root_path is not None:
        command_targets = {
            "scripts/validate_registry.py",
            "scripts/replay_experiment.py",
            "tests",
            "Navier/AxiomAudit.lean",
        }
        for relative in sorted(command_targets):
            target = root_path / relative
            if not target.exists() or target.is_symlink():
                errors.append(f"$.verifiers: canonical verifier command target is missing or unsafe: {relative}")
    evidence = _validate_evidence(
        top.get("evidence"),
        references,
        verifiers,
        base_revision,
        now_utc,
        root_path,
        check_git_revision,
        errors,
    )
    obligations = _validate_obligations_shape(
        top.get("obligations"), approaches, barriers, references, evidence, verifiers, errors
    )
    _validate_pinned_obligation_contracts(obligations, errors)

    all_ids: list[str] = [
        item_id
        for item_id in (top.get("registry_id"), campaign.get("id"))
        if isinstance(item_id, str)
    ]
    for collection in (references, barriers, approaches, verifiers, evidence, obligations):
        all_ids.extend(collection)
    duplicates = sorted(item_id for item_id, count in Counter(all_ids).items() if count > 1)
    if duplicates:
        errors.append(f"$: identifiers must be globally unique; duplicates={duplicates}")

    for evidence_id, item in evidence.items():
        for supported_id in item.get("supports", []):
            if supported_id not in obligations:
                errors.append(f"$.evidence[{evidence_id}].supports: unknown obligation {supported_id!r}")

    _validate_graph_and_epistemics(
        campaign,
        approaches,
        obligations,
        evidence,
        verifiers,
        base_revision,
        root_path,
        check_native_receipts,
        errors,
    )
    return ValidationResult(tuple(dict.fromkeys(errors)))


def validate_registry_file(
    registry_path: str | Path,
    *,
    now: datetime | None = None,
    check_git_revision: bool = True,
) -> tuple[dict[str, Any], ValidationResult]:
    """Load a registry, confirm its declared schema, and validate it."""

    path = Path(registry_path).resolve()
    data = load_json(path)
    errors: list[str] = []
    if not isinstance(data, dict):
        return {}, ValidationResult(("$: expected object",))
    schema_ref = data.get("$schema")
    if schema_ref != SCHEMA_REF:
        errors.append(f"$.$schema: expected {SCHEMA_REF!r}")
    else:
        schema_path = (path.parent / schema_ref).resolve()
        try:
            schema = load_json(schema_path)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            errors.append(f"$.$schema: cannot load declared schema: {exc}")
        else:
            declared = schema.get("properties", {}).get("schema_version", {}).get("const")
            if declared != SCHEMA_VERSION:
                errors.append(f"$.$schema: schema const is {declared!r}, expected {SCHEMA_VERSION!r}")
            if schema.get("additionalProperties") is not False:
                errors.append("$.$schema: top-level schema must fail closed on unknown properties")
    result = validate_registry(
        data,
        now=now,
        repo_root=path.parent.parent,
        check_git_revision=check_git_revision,
    )
    return data, ValidationResult(tuple(dict.fromkeys(errors + list(result.errors))))


def assert_valid_registry(
    data: Any,
    *,
    now: datetime | None = None,
    repo_root: str | Path | None = None,
    check_git_revision: bool = True,
) -> None:
    """Raise ``RegistryValidationError`` unless the registry is fully valid."""

    result = validate_registry(
        data,
        now=now,
        repo_root=repo_root,
        check_git_revision=check_git_revision,
    )
    if not result.valid:
        raise RegistryValidationError(result.errors)


def derived_status(data: dict[str, Any]) -> dict[str, Any]:
    """Derive a deterministic status view from an already validated registry."""

    obligations = data["obligations"]
    approaches = data["approaches"]
    dispositions = Counter(node["disposition"] for node in obligations)
    tiers = Counter(node["claim_tier"] for node in obligations)
    endpoints = [
        {
            "id": node["id"],
            "branch": node["domain"]["endpoint_branch"],
            "disposition": node["disposition"],
            "residual": node["residual"]["statement"] if node["residual"] else None,
        }
        for node in obligations
        if node["id"] in data["campaign"]["resolution_obligation_ids"]
    ]
    approach_rows = []
    for approach in approaches:
        nodes = [node for node in obligations if node["approach_id"] == approach["id"]]
        approach_rows.append(
            {
                "id": approach["id"],
                "status": approach["status"],
                "obligation_count": len(nodes),
                "closed": sum(node["disposition"] == "CLOSED" for node in nodes),
                "open": sum(node["disposition"] not in {"CLOSED", "FALSIFIED", "REVERTED"} for node in nodes),
                "blocked_barriers": sorted(
                    review["barrier_id"]
                    for review in approach["barrier_reviews"]
                    if review["disposition"] == "BLOCKED"
                ),
            }
        )
    return {
        "registry_id": data["registry_id"],
        "registry_version": data["registry_version"],
        "base_revision": data["base_revision"],
        "global_disposition": data["campaign"]["global_disposition"],
        "scientific_status": data["campaign"]["scientific_status"],
        "dispositions": dict(sorted(dispositions.items())),
        "claim_tiers": dict(sorted(tiers.items())),
        "endpoints": endpoints,
        "approaches": approach_rows,
    }


def clone_registry(data: dict[str, Any]) -> dict[str, Any]:
    """Deep-copy helper used by hostile tests without mutating the SSOT."""

    return copy.deepcopy(data)
