"""Regression witnesses from the independent registry and replay audit.

Each case starts from a valid shape, introduces one hostile mutation, and
asserts the validator's fail-closed reason.  Runtime replay fixtures live only
in auto-removed temporary Git repositories; they never execute in this tree.
"""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import textwrap
import unittest
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from registry_core import validate_registry  # noqa: E402
from replay_experiment import ManifestError, replay, validate_manifest  # noqa: E402
from tests import test_registry as registry_fixtures  # noqa: E402


EXPERIMENT_ID = "computation.intermediate_falsification"
SANDBOX_AVAILABLE = (
    sys.platform == "darwin"
    and Path("/usr/bin/sandbox-exec").is_file()
    and not Path("/usr/bin/sandbox-exec").is_symlink()
)


def _sha256(payload: bytes | str) -> str:
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _experiment_obligation(registry: dict[str, object]) -> dict[str, object]:
    return copy.deepcopy(registry_fixtures._find(registry["obligations"], EXPERIMENT_ID))


def _manifest(
    registry: dict[str, object],
    *,
    revision: str = "a" * 40,
    driver_source: str = "print('ok')\n",
    stdout: bytes = b"ok\n",
    output: bytes = b"result\n",
) -> dict[str, object]:
    obligation = _experiment_obligation(registry)
    return {
        "schema_version": "navier.experiment_run@1.0.0",
        "experiment_id": "experiment.audit_regression",
        "obligation_id": EXPERIMENT_ID,
        "generated_at": "2026-07-14T18:00:00Z",
        "repository_revision": revision,
        "epistemic_status": "OBSERVATION_ONLY",
        "closes_clay_endpoint": False,
        "model": copy.deepcopy(obligation["domain"]),
        "run": {
            "command": ["python3", "experiments/audit_driver.py"],
            "driver_path": "experiments/audit_driver.py",
            "driver_sha256": _sha256(driver_source),
            "seed": 17,
            "precision": "binary64",
            "truncation": "8x8x8 divergence-free Fourier grid",
            "expected_exit_code": 0,
            "stdout_sha256": _sha256(stdout),
        },
        "artifacts": [
            {
                "role": "OUTPUT",
                "path": "artifacts/runs/audit/result.txt",
                "sha256": _sha256(output),
            }
        ],
    }


def _run_git(repo: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-c", "core.hooksPath=/dev/null", *args],
        cwd=repo,
        text=True,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(completed.stderr or completed.stdout)
    return completed.stdout.strip()


@contextmanager
def _temporary_repository(
    registry: dict[str, object],
    driver_source: str,
    *,
    track_driver: bool = True,
    preexisting_output: bytes | None = None,
) -> Iterator[tuple[Path, str]]:
    with tempfile.TemporaryDirectory(prefix="navier-audit-replay-") as temporary:
        repo = Path(temporary)
        registry_path = repo / "data" / "attack_registry.json"
        driver_path = repo / "experiments" / "audit_driver.py"
        registry_path.parent.mkdir(parents=True)
        driver_path.parent.mkdir(parents=True)
        registry_path.write_text(json.dumps(registry), encoding="utf-8")
        if track_driver:
            driver_path.write_text(driver_source, encoding="utf-8")

        _run_git(repo, "init", "--quiet")
        _run_git(repo, "config", "user.email", "audit-regression@example.invalid")
        _run_git(repo, "config", "user.name", "Navier Audit Regression")
        _run_git(repo, "add", "data/attack_registry.json")
        if track_driver:
            _run_git(repo, "add", "experiments/audit_driver.py")
        _run_git(repo, "commit", "--quiet", "-m", "pinned replay fixture")
        revision = _run_git(repo, "rev-parse", "HEAD")

        if not track_driver:
            driver_path.write_text(driver_source, encoding="utf-8")
        if preexisting_output is not None:
            output_path = repo / "artifacts" / "runs" / "audit" / "result.txt"
            output_path.parent.mkdir(parents=True)
            output_path.write_bytes(preexisting_output)
        yield repo, revision


class RegistryAuditRegressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.canonical = registry_fixtures.load_json(registry_fixtures.REGISTRY_PATH)
        cls.valid_fixture = registry_fixtures.make_valid_fixture(cls.canonical)
        registry_fixtures._find(
            cls.valid_fixture["obligations"], registry_fixtures.A_ID
        )["formal_declaration"] = None
        baseline = validate_registry(
            cls.valid_fixture,
            now=registry_fixtures.NOW,
            check_git_revision=False,
        )
        if not baseline.valid:
            raise AssertionError("invalid hostile-test baseline:\n" + "\n".join(baseline.errors))

    def setUp(self) -> None:
        self.registry = copy.deepcopy(self.valid_fixture)

    def assertRejected(self, *fragments: str) -> str:
        result = validate_registry(
            self.registry,
            now=registry_fixtures.NOW,
            check_git_revision=False,
        )
        rendered = "\n".join(result.errors)
        self.assertFalse(result.valid, "hostile registry unexpectedly validated")
        for fragment in fragments:
            self.assertIn(fragment, rendered)
        return rendered

    def test_endpoint_target_definition_cannot_be_its_own_realization_proof(self) -> None:
        endpoint = registry_fixtures._find(
            self.registry["obligations"], registry_fixtures.A_ID
        )
        target = self.registry["campaign"]["problem_surface"]["resolution_branches"][0][
            "public_declaration"
        ]
        endpoint["formal_declaration"] = target
        evidence = registry_fixtures._native_evidence(self.registry)
        evidence["receipt"]["declaration"] = target
        registry_fixtures._close_a(self.registry, evidence)

        self.assertRejected("endpoint target definition cannot serve as its realization proof")

    def test_self_asserted_native_receipt_cannot_close_endpoint(self) -> None:
        endpoint = registry_fixtures._find(
            self.registry["obligations"], registry_fixtures.A_ID
        )
        endpoint["formal_declaration"] = "Navier.Audit.syntheticStatementAProof"
        evidence = registry_fixtures._native_evidence(self.registry)
        evidence["provenance"]["source_locator"] = "artifact:missing-self-asserted-receipt.json"
        evidence["receipt"]["declaration"] = "Navier.Audit.syntheticStatementAProof"
        registry_fixtures._close_a(self.registry, evidence)

        self.assertRejected("native receipt was not freshly revalidated")

    def test_experiment_taint_cannot_hide_behind_closed_meta_node(self) -> None:
        endpoint = registry_fixtures._find(
            self.registry["obligations"], registry_fixtures.A_ID
        )
        experiment = copy.deepcopy(endpoint)
        experiment.update(
            {
                "id": "experiment.audit_taint",
                "title": "Exact-domain experiment used as hostile proof-path input",
                "kind": "EXPERIMENT",
                "claim_tier": "EXPERIMENT",
                "disposition": "CLOSED",
                "formal_declaration": None,
                "dependency_mode": "NONE",
                "dependencies": [],
                "assumption_ids": [],
                "evidence_links": [],
                "verifier_ids": ["verifier.experiment.replay"],
                "residual": None,
            }
        )
        meta = copy.deepcopy(experiment)
        meta.update(
            {
                "id": "meta.audit_launderer",
                "title": "Closed metadata wrapper around experimental input",
                "kind": "META",
                "claim_tier": "SCAFFOLD",
                "dependency_mode": "ALL",
                "dependencies": [experiment["id"]],
                "verifier_ids": ["verifier.registry.strict"],
            }
        )
        self.registry["obligations"].extend([experiment, meta])
        endpoint["dependency_mode"] = "ALL"
        endpoint["dependencies"] = [meta["id"]]

        self.assertRejected("experiment-tainted proof path")

    def test_weak_solution_class_cannot_label_exact_endpoint(self) -> None:
        endpoint = registry_fixtures._find(
            self.registry["obligations"], registry_fixtures.A_ID
        )
        endpoint["domain"]["solution_class"] = "DISTRIBUTIONAL_WEAK"

        self.assertRejected("endpoint must use EXACT_SMOOTH_FINITE_ENERGY")

    def test_closed_approach_cannot_hide_open_obligation(self) -> None:
        approach = registry_fixtures._find(
            self.registry["approaches"], "approach.exact_semantics_local_theory"
        )
        approach["status"] = "CLOSED"

        self.assertRejected("CLOSED approach requires every obligation CLOSED")

    def test_unrelated_native_theorem_cannot_close_frequency_approach(self) -> None:
        hostile = copy.deepcopy(self.canonical)
        node = registry_fixtures._find(
            hostile["obligations"], "frequency.cascade_exclusion"
        )
        node.update(
            {
                "claim_tier": "THEOREM",
                "disposition": "CLOSED",
                "formal_declaration": "Navier.Scaling.mixedNormExponent_eq_zero_iff",
                "residual": None,
            }
        )
        registry_fixtures._find(
            hostile["approaches"], "approach.frequency_cascade"
        )["status"] = "CLOSED"
        evidence = registry_fixtures._native_evidence(
            hostile,
            node_id="frequency.cascade_exclusion",
        )
        evidence["receipt"]["declaration"] = node["formal_declaration"]
        hostile["evidence"].append(evidence)
        node["evidence_links"] = [
            {"evidence_id": evidence["id"], "role": "REALIZATION"}
        ]

        result = validate_registry(
            hostile,
            now=registry_fixtures.NOW,
            check_git_revision=False,
            check_native_receipts=False,
        )
        rendered = "\n".join(result.errors)
        self.assertFalse(result.valid, "unrelated theorem unexpectedly closed an approach")
        self.assertIn("immutable semantic/formal contract mismatch", rendered)
        self.assertIn("internal closure has no immutable formal realization contract", rendered)

    def test_renamed_meta_alias_cannot_close_frequency_approach(self) -> None:
        hostile = copy.deepcopy(self.canonical)
        node = registry_fixtures._find(
            hostile["obligations"], "frequency.cascade_exclusion"
        )
        node.update(
            {
                "id": "meta.frequency_closed_alias",
                "kind": "META",
                "claim_tier": "SCAFFOLD",
                "disposition": "CLOSED",
                "formal_declaration": None,
                "evidence_links": [],
                "residual": None,
            }
        )
        consumer = registry_fixtures._find(
            hostile["obligations"], "regularity.any_positive_route"
        )
        consumer["dependencies"].remove("frequency.cascade_exclusion")
        registry_fixtures._find(
            hostile["approaches"], "approach.frequency_cascade"
        )["status"] = "CLOSED"

        result = validate_registry(
            hostile,
            now=registry_fixtures.NOW,
            check_git_revision=False,
        )
        rendered = "\n".join(result.errors)
        self.assertFalse(result.valid, "renamed metadata alias unexpectedly closed an approach")
        self.assertIn("canonical obligation set mismatch", rendered)
        self.assertIn("immutable semantic/formal contract mismatch", rendered)
        self.assertIn(
            "only formal obligations with native realization evidence may use CLOSED",
            rendered,
        )

    def test_compound_primary_evidence_requires_source_specific_provenance(self) -> None:
        hostile = copy.deepcopy(self.canonical)
        evidence = registry_fixtures._find(
            hostile["evidence"], "evidence.breakdown.weak_nonuniqueness_warning"
        )
        evidence["reference_ids"].append("ref.tao.averaged2016")

        result = validate_registry(
            hostile,
            now=registry_fixtures.NOW,
            check_git_revision=False,
        )
        rendered = "\n".join(result.errors)
        self.assertFalse(result.valid, "compound provenance unexpectedly validated")
        self.assertIn("requires exactly one source-specific provenance record", rendered)

    def test_cached_campaign_status_cannot_outrun_open_endpoints(self) -> None:
        self.registry["campaign"]["global_disposition"] = "DECOMPOSED"
        self.registry["campaign"]["scientific_status"] = "CONDITIONAL_FRONTIER"

        self.assertRejected("open campaign must remain SCAFFOLDED / SCIENTIFIC_FRONTIER")

    def test_campaign_identifier_collision_is_globally_rejected(self) -> None:
        colliding_id = registry_fixtures.A_ID
        self.registry["campaign"]["id"] = colliding_id
        campaign_consumer = f"campaign:{colliding_id}"
        for endpoint in self.registry["obligations"]:
            endpoint["residual"]["consumer_ids"] = [campaign_consumer]

        self.assertRejected("identifiers must be globally unique", colliding_id)

    def test_shell_prefixed_lean_verifier_breaks_canonical_contract(self) -> None:
        verifier = registry_fixtures._verifier(self.registry, "verifier.lean.native")
        verifier["command"] = "sh -c 'lake env lean Navier.lean'"

        self.assertRejected("canonical verifier contract mismatch")

    def test_nonexistent_replay_verifier_breaks_canonical_contract(self) -> None:
        verifier = registry_fixtures._verifier(
            self.registry, "verifier.experiment.replay"
        )
        verifier["command"] = "python3 scripts/does_not_exist.py artifacts/runs/experiment.json"

        self.assertRejected("canonical verifier contract mismatch")

    def test_closed_claim_cannot_rest_on_open_assumption(self) -> None:
        assumption = copy.deepcopy(
            registry_fixtures._find(self.registry["obligations"], registry_fixtures.A_ID)
        )
        assumption.update(
            {
                "id": "assumption.audit_open",
                "title": "Open analytic assumption for hostile closure test",
                "kind": "PAYLOAD",
                "claim_tier": "CONJECTURE",
                "formal_declaration": None,
                "dependency_mode": "NONE",
                "dependencies": [],
                "assumption_ids": [],
                "residual": registry_fixtures._residual("FEFFERMAN_A"),
            }
        )
        closed = copy.deepcopy(assumption)
        closed.update(
            {
                "id": "theorem.audit_assumption_backed",
                "title": "Hostile closed theorem backed by an open assumption",
                "kind": "THEOREM",
                "claim_tier": "THEOREM",
                "disposition": "CLOSED",
                "formal_declaration": "Navier.Audit.assumptionBackedProof",
                "assumption_ids": [assumption["id"]],
                "residual": None,
            }
        )
        assumption["residual"]["consumer_ids"] = [closed["id"]]
        self.registry["obligations"].extend([assumption, closed])
        evidence = registry_fixtures._native_evidence(
            self.registry, node_id=closed["id"]
        )
        evidence["receipt"]["declaration"] = closed["formal_declaration"]
        self.registry["evidence"].append(evidence)
        closed["evidence_links"] = [
            {"evidence_id": evidence["id"], "role": "REALIZATION"}
        ]

        self.assertRejected("CLOSED obligation cannot be assumption-backed")

    def test_lean_verifier_cannot_drop_base_kernel_axiom_policy(self) -> None:
        schema = registry_fixtures.load_json(registry_fixtures.SCHEMA_PATH)
        schema_policy = schema["$defs"]["verifier"]["allOf"][0]["then"][
            "properties"
        ]["allowed_axioms"]
        self.assertGreaterEqual(schema_policy["minItems"], 3)
        required_by_schema = {
            clause["contains"]["const"] for clause in schema_policy["allOf"]
        }
        self.assertEqual(
            required_by_schema,
            {"propext", "Classical.choice", "Quot.sound"},
        )
        verifier = registry_fixtures._verifier(self.registry, "verifier.lean.native")
        verifier["allowed_axioms"] = []

        self.assertRejected("LEAN_NATIVE allowed axioms must include the base kernel policy")


class ReplayAuditRegressionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.registry = registry_fixtures.load_json(registry_fixtures.REGISTRY_PATH)

    def assertManifestRejected(
        self,
        manifest: dict[str, object],
        fragment: str,
        *,
        repo_root: Path = ROOT,
        check_files: bool = False,
        check_git: bool = False,
    ) -> str:
        with self.assertRaises(ManifestError) as raised:
            validate_manifest(
                manifest,
                repo_root=repo_root,
                registry=self.registry,
                check_files=check_files,
                check_git=check_git,
            )
        rendered = str(raised.exception)
        self.assertIn(fragment, rendered)
        return rendered

    def test_incomplete_model_identity_is_rejected(self) -> None:
        manifest = _manifest(self.registry)
        del manifest["model"]["solution_class"]

        self.assertManifestRejected(
            manifest,
            "$.model: missing solution_class; missing fields ['solution_class']",
        )

    def test_parent_traversal_command_argument_is_rejected(self) -> None:
        manifest = _manifest(self.registry)
        manifest["run"]["command"].append("../../outside-repository")

        self.assertManifestRejected(
            manifest,
            "$.run.command[2]: unsafe repository path argument; unsafe command argument",
        )

    def test_untracked_driver_cannot_claim_pinned_revision(self) -> None:
        driver_source = "print('ok')\n"
        output = b"result\n"
        with _temporary_repository(
            self.registry,
            driver_source,
            track_driver=False,
            preexisting_output=output,
        ) as (repo, revision):
            manifest = _manifest(
                self.registry,
                revision=revision,
                driver_source=driver_source,
                output=output,
            )
            self.assertManifestRejected(
                manifest,
                "$.run.driver_path: driver is not tracked at repository revision; "
                "path is not tracked at the declared revision",
                repo_root=repo,
                check_files=True,
                check_git=True,
            )

    @unittest.skipUnless(SANDBOX_AVAILABLE, "sandbox-exec confinement is unavailable")
    def test_replay_rejects_undeclared_filesystem_output(self) -> None:
        driver_source = textwrap.dedent(
            """\
            from pathlib import Path

            declared = Path("artifacts/runs/audit/result.txt")
            declared.parent.mkdir(parents=True, exist_ok=True)
            declared.write_text("result\\n", encoding="utf-8")
            undeclared = Path("escape.txt")
            undeclared.write_text("undeclared\\n", encoding="utf-8")
            print("ok")
            """
        )
        with _temporary_repository(self.registry, driver_source) as (repo, revision):
            manifest = _manifest(
                self.registry,
                revision=revision,
                driver_source=driver_source,
            )
            with self.assertRaises(ManifestError) as raised:
                replay(manifest, repo_root=repo)
            self.assertIn(
                "$.run.command: undeclared filesystem output at 'escape.txt'; "
                "undeclared filesystem mutation",
                str(raised.exception),
            )

    @unittest.skipUnless(SANDBOX_AVAILABLE, "sandbox-exec confinement is unavailable")
    def test_noop_cannot_reuse_preexisting_declared_output(self) -> None:
        driver_source = "print('ok')\n"
        output = b"result\n"
        with _temporary_repository(
            self.registry,
            driver_source,
            preexisting_output=output,
        ) as (repo, revision):
            manifest = _manifest(
                self.registry,
                revision=revision,
                driver_source=driver_source,
                output=output,
            )
            with self.assertRaises(ManifestError) as raised:
                replay(manifest, repo_root=repo)
            self.assertIn(
                "$.artifacts[0]: OUTPUT must be freshly produced; "
                "expected a regular non-symlink file",
                str(raised.exception),
            )


if __name__ == "__main__":
    unittest.main()
