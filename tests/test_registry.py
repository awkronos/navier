"""Adversarial tests for the Navier attack registry and dossier.

The hostile cases deliberately start from a small valid registry assembled as
a deep copy of the canonical metadata.  This keeps each failure focused even
while the scientific registry grows new obligations.
"""

from __future__ import annotations

import copy
import re
import sys
import tempfile
import unittest
from datetime import UTC, datetime, timedelta
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from registry_core import (  # noqa: E402
    derived_status,
    load_json,
    validate_registry,
    validate_registry_file,
)
from render_status import _render_text  # noqa: E402


REGISTRY_PATH = ROOT / "data" / "attack_registry.json"
SCHEMA_PATH = ROOT / "schemas" / "attack_registry.schema.json"
ATTACK_PATH = ROOT / "docs" / "ATTACK.md"
MANIFEST_PATH = ROOT / "references" / "manifest.json"
NOW = datetime(2026, 7, 14, 23, 0, tzinfo=UTC)

A_ID = "endpoint.fefferman_a"
C_ID = "endpoint.fefferman_c"
CAMPAIGN_CONSUMER = "campaign:campaign.navier_clay"


def _residual(branch: str) -> dict[str, object]:
    return {
        "statement": f"Construct the missing exact {branch} realization without endpoint assumptions.",
        "smaller_than": f"This requests one branch-specific realization rather than the full {branch} endpoint.",
        "consumer_ids": [CAMPAIGN_CONSUMER],
        "falsifier": f"A checked wrong-domain or circular {branch} construction falsifies this route.",
        "next_action": f"Formalize and audit the next exact {branch} realization payload.",
    }


def make_valid_fixture(canonical: dict[str, object]) -> dict[str, object]:
    """Make a deterministic valid copy of the exact canonical closed-world registry."""

    registry = copy.deepcopy(canonical)
    registry["generated_at"] = NOW.isoformat().replace("+00:00", "Z")
    return registry


def _find(items: list[dict[str, object]], item_id: str) -> dict[str, object]:
    return next(item for item in items if item["id"] == item_id)


def _verifier(registry: dict[str, object], verifier_id: str) -> dict[str, object]:
    return _find(registry["verifiers"], verifier_id)


def _native_evidence(
    registry: dict[str, object],
    *,
    node_id: str = A_ID,
    generated_at: datetime = NOW,
) -> dict[str, object]:
    verifier = _verifier(registry, "verifier.lean.native")
    digest = "a" * 64
    return {
        "id": "evidence.native_test",
        "kind": "NATIVE_RECEIPT",
        "claim_tier": "THEOREM",
        "summary": "A native compiler and axiom-audit receipt for the exact formal declaration.",
        "reference_ids": ["ref.clay.fefferman2000"],
        "supports": [node_id],
        "provenance": {
            "source_locator": "artifact:native-test-receipt",
            "source_revision": registry["base_revision"],
            "immutable": True,
            "observed_at": generated_at.isoformat(),
            "artifact_sha256": digest,
        },
        "receipt": {
            "verifier_id": verifier["id"],
            "command": verifier["command"],
            "exit_code": 0,
            "result": "PASS",
            "generated_at": generated_at.isoformat(),
            "repository_revision": registry["base_revision"],
            "declaration": "Navier.Clay.StatementAProof",
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
            "artifact_sha256": digest,
        },
    }


def _experiment_evidence(registry: dict[str, object]) -> dict[str, object]:
    verifier = _verifier(registry, "verifier.experiment.replay")
    digest = "b" * 64
    return {
        "id": "evidence.experiment_test",
        "kind": "EXPERIMENT_RECEIPT",
        "claim_tier": "EXPERIMENT",
        "summary": "A reproducible numerical observation that cannot realize a theorem claim.",
        "reference_ids": ["ref.clay.fefferman2000"],
        "supports": [A_ID],
        "provenance": {
            "source_locator": "artifact:experiment-test-receipt",
            "source_revision": "experiment-run-0001",
            "immutable": True,
            "observed_at": NOW.isoformat(),
            "artifact_sha256": digest,
        },
        "receipt": {
            "verifier_id": verifier["id"],
            "command": verifier["command"],
            "exit_code": 0,
            "result": "PASS",
            "generated_at": NOW.isoformat(),
            "repository_revision": registry["base_revision"],
            "declaration": None,
            "axioms": [],
            "artifact_sha256": digest,
        },
    }


def _surface_snapshot(registry: dict[str, object]) -> dict[str, object]:
    return {
        "id": "evidence.generated_snapshot",
        "kind": "FORMAL_SURFACE_SNAPSHOT",
        "claim_tier": "SCAFFOLD",
        "summary": "A generated formal-surface snapshot that records syntax but proves no theorem.",
        "reference_ids": ["ref.clay.fefferman2000"],
        "supports": [A_ID],
        "provenance": {
            "source_locator": "artifact:generated-formal-surface",
            "source_revision": registry["base_revision"],
            "immutable": True,
            "observed_at": NOW.isoformat(),
            "artifact_sha256": "c" * 64,
        },
        "receipt": None,
    }


def _falsification_witness(registry: dict[str, object]) -> dict[str, object]:
    return {
        "id": "evidence.falsification_test",
        "kind": "FALSIFICATION_WITNESS",
        "claim_tier": "FALSIFICATION",
        "summary": "A checked counterexample witness falsifying the selected route without claiming closure.",
        "reference_ids": ["ref.clay.fefferman2000"],
        "supports": [A_ID],
        "provenance": {
            "source_locator": "artifact:falsification-test-witness",
            "source_revision": registry["base_revision"],
            "immutable": True,
            "observed_at": NOW.isoformat(),
            "artifact_sha256": "f" * 64,
        },
        "receipt": None,
    }


def _close_a(registry: dict[str, object], evidence: dict[str, object] | None = None) -> None:
    node = _find(registry["obligations"], A_ID)
    node["disposition"] = "CLOSED"
    if node["formal_declaration"] is None:
        node["formal_declaration"] = "Navier.Clay.StatementAProof"
    node["residual"] = None
    if evidence is not None:
        registry["evidence"].append(evidence)
        node["evidence_links"].append({"evidence_id": evidence["id"], "role": "REALIZATION"})
    registry["campaign"]["global_disposition"] = "CLOSED"
    registry["campaign"]["scientific_status"] = "FORMALLY_RESOLVED"


class RegistryTestCase(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.canonical = load_json(REGISTRY_PATH)
        cls.valid_fixture = make_valid_fixture(cls.canonical)

    def setUp(self) -> None:
        self.registry = copy.deepcopy(self.valid_fixture)

    def assertValid(self, registry: dict[str, object] | None = None) -> None:
        result = validate_registry(
            registry or self.registry,
            now=NOW,
            check_git_revision=False,
        )
        self.assertTrue(result.valid, "\n".join(result.errors))

    def assertInvalid(self, *fragments: str) -> str:
        result = validate_registry(self.registry, now=NOW, check_git_revision=False)
        text = "\n".join(result.errors)
        self.assertFalse(result.valid, "hostile registry unexpectedly validated")
        for fragment in fragments:
            self.assertIn(fragment, text)
        return text


class PositiveAndClosedWorldTests(RegistryTestCase):
    def test_independent_deep_copy_fixture_is_valid(self) -> None:
        self.assertIsNot(self.registry, self.valid_fixture)
        self.assertValid()

    def test_canonical_registry_loads_and_validates(self) -> None:
        data, result = validate_registry_file(REGISTRY_PATH, now=NOW)
        self.assertEqual(data["registry_id"], "navier.attack_registry")
        self.assertTrue(result.valid, "\n".join(result.errors))

    def test_duplicate_json_keys_are_rejected_at_load(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "duplicate.json"
            path.write_text('{"registry_id": "first", "registry_id": "second"}', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate JSON key 'registry_id'"):
                load_json(path)

    def test_unknown_top_level_key_is_rejected(self) -> None:
        self.registry["optimistic_status"] = "PROVED"
        self.assertInvalid("$: unknown fields ['optimistic_status']")

    def test_unknown_nested_key_is_rejected(self) -> None:
        self.registry["campaign"]["proof_by_press_release"] = True
        self.assertInvalid("$.campaign: unknown fields ['proof_by_press_release']")

    def test_silent_required_field_omission_is_rejected(self) -> None:
        del self.registry["ssot"]
        self.assertInvalid("$: missing fields ['ssot']")

    def test_schema_version_drift_is_rejected(self) -> None:
        self.registry["schema_version"] = "1.1.0"
        self.assertInvalid("$.schema_version: expected '1.0.0'")

    def test_future_registry_generated_at_is_rejected(self) -> None:
        self.registry["generated_at"] = (NOW + timedelta(seconds=1)).isoformat()
        self.assertInvalid("registry timestamp is from the future")

    def test_schema_reference_drift_is_rejected(self) -> None:
        self.registry["$schema"] = "../schemas/latest.json"
        self.assertInvalid("$.$schema: expected '../schemas/attack_registry.schema.json'")

    def test_deletion_overbroad_missing_canonical_approach_is_rejected(self) -> None:
        self.registry["approaches"].pop()
        self.assertInvalid("canonical attack lanes mismatch", "approach.breakdown_construction")

    def test_cleanup_rename_of_canonical_barrier_is_rejected(self) -> None:
        self.registry["barriers"][0]["id"] = "barrier.renamed_endpoint_semantics"
        self.assertInvalid("canonical barrier set mismatch", "barrier.endpoint_semantics")

    def test_global_identifier_collision_is_rejected(self) -> None:
        self.registry["verifiers"][0]["id"] = self.registry["references"][0]["id"]
        self.assertInvalid("identifiers must be globally unique")

    def test_obligation_nonclosed_disposition_drift_is_rejected(self) -> None:
        _find(self.registry["obligations"], "critical.unconditional_bound")[
            "disposition"
        ] = "DECOMPOSED"
        self.assertInvalid("canonical open disposition mismatch; expected 'SCAFFOLDED'")

    def test_approach_nonclosed_disposition_drift_is_rejected(self) -> None:
        _find(self.registry["approaches"], "approach.critical_norms")["status"] = (
            "DECOMPOSED"
        )
        self.assertInvalid(
            "canonical nonclosed disposition mismatch; expected 'SCAFFOLDED'"
        )


class EndpointAndDomainTests(RegistryTestCase):
    def test_fefferman_a_forcing_drift_is_rejected(self) -> None:
        self.registry["campaign"]["problem_surface"]["resolution_branches"][0]["forcing"] = "SMOOTH_RAPID_DECAY"
        self.assertInvalid("FEFFERMAN_A forcing must be ZERO")

    def test_fefferman_c_forcing_drift_is_rejected(self) -> None:
        self.registry["campaign"]["problem_surface"]["resolution_branches"][1]["forcing"] = "ZERO"
        self.assertInvalid("FEFFERMAN_C forcing must be SMOOTH_RAPID_DECAY")

    def test_problem_surface_viscosity_drift_is_rejected(self) -> None:
        self.registry["campaign"]["problem_surface"]["viscosity"] = "ZERO"
        self.assertInvalid("$.campaign.problem_surface.viscosity: expected 'POSITIVE'")

    def test_fefferman_c_declaration_laundering_is_rejected(self) -> None:
        branch = self.registry["campaign"]["problem_surface"]["resolution_branches"][1]
        branch["public_declaration"] = "Navier.Clay.StatementC"
        branch["planned_formal_target"] = None
        _find(self.registry["obligations"], C_ID)["formal_declaration"] = "Navier.Clay.StatementC"
        self.assertInvalid("Fefferman C must remain an explicit planned target until delivered")

    def test_fefferman_a_delivered_declaration_cannot_be_demoted_to_planned(self) -> None:
        branch = self.registry["campaign"]["problem_surface"]["resolution_branches"][0]
        branch["public_declaration"] = None
        branch["planned_formal_target"] = "Navier.Clay.StatementA"
        _find(self.registry["obligations"], A_ID)["formal_declaration"] = None
        self.assertInvalid("Fefferman A must bind the delivered Navier.Clay.StatementA")

    def test_wrong_equation_on_endpoint_path_is_rejected(self) -> None:
        _find(self.registry["obligations"], A_ID)["domain"]["equation"] = "AVERAGED_NAVIER_STOKES"
        self.assertInvalid("wrong object on FEFFERMAN_A proof path")

    def test_wrong_geometry_on_endpoint_path_is_rejected(self) -> None:
        _find(self.registry["obligations"], C_ID)["domain"]["geometry"] = "TORUS3"
        self.assertInvalid("wrong object on FEFFERMAN_C proof path")

    def test_approximation_relation_on_exact_endpoint_is_rejected(self) -> None:
        _find(self.registry["obligations"], A_ID)["domain"]["relation_to_endpoint"] = "APPROXIMATION_ONLY"
        self.assertInvalid("endpoint must have exact FEFFERMAN_A domain", "wrong-domain node")

    def test_branch_specific_endpoint_force_is_checked_against_domain(self) -> None:
        _find(self.registry["obligations"], C_ID)["domain"]["forcing"] = "ZERO"
        self.assertInvalid("FEFFERMAN_C requires SMOOTH_RAPID_DECAY")


class GraphAndResidualTests(RegistryTestCase):
    def test_dependency_cycle_is_rejected(self) -> None:
        a = _find(self.registry["obligations"], A_ID)
        c = _find(self.registry["obligations"], C_ID)
        a["dependency_mode"], a["dependencies"] = "ALL", [C_ID]
        c["dependency_mode"], c["dependencies"] = "ALL", [A_ID]
        self.assertInvalid("dependency/assumption cycle detected")

    def test_dangling_dependency_is_rejected(self) -> None:
        a = _find(self.registry["obligations"], A_ID)
        a["dependency_mode"] = "ALL"
        a["dependencies"] = ["payload.missing_realization"]
        self.assertInvalid("unknown obligation 'payload.missing_realization'")

    def test_dangling_residual_consumer_is_rejected(self) -> None:
        a = _find(self.registry["obligations"], A_ID)
        a["residual"]["consumer_ids"] = ["consumer.missing"]
        self.assertInvalid("unknown consumer 'consumer.missing'")

    def test_declared_consumer_must_actually_consume_obligation(self) -> None:
        a = _find(self.registry["obligations"], A_ID)
        a["residual"]["consumer_ids"] = [C_ID]
        self.assertInvalid(f"{C_ID!r} does not consume this obligation")

    def test_residual_repeating_parent_obligation_is_rejected(self) -> None:
        a = _find(self.registry["obligations"], A_ID)
        a["residual"]["statement"] = a["statement"]
        self.assertInvalid("residual merely repeats the parent obligation")

    def test_vacuous_payload_is_rejected(self) -> None:
        _find(self.registry["obligations"], A_ID)["residual"]["statement"] = "True"
        self.assertInvalid("vacuous text is forbidden")

    def test_wrapper_payload_laundering_phrase_is_rejected(self) -> None:
        _find(self.registry["obligations"], A_ID)["statement"] = (
            "Assume the Clay endpoint and package the desired result as a bridge."
        )
        self.assertInvalid("endpoint/wrapper laundering phrase is forbidden")

    def test_public_endpoint_cannot_be_an_assumption(self) -> None:
        a = _find(self.registry["obligations"], A_ID)
        a["assumption_ids"] = [C_ID]
        self.assertInvalid("endpoint-as-assumption is forbidden", "public endpoint cannot be assumption-backed")

    def test_experiment_obligation_cannot_feed_a_formal_dependency(self) -> None:
        experiment = copy.deepcopy(_find(self.registry["obligations"], A_ID))
        experiment.update(
            {
                "id": "experiment.discrete_probe",
                "title": "Discrete observation-only probe",
                "kind": "EXPERIMENT",
                "claim_tier": "EXPERIMENT",
                "formal_declaration": None,
            }
        )
        experiment["domain"].update(
            {
                "equation": "DISCRETE_NAVIER_STOKES",
                "geometry": "DISCRETE_GRID",
                "boundary": "DISCRETE",
                "forcing": "DISCRETE",
                "viscosity": "DISCRETE_POSITIVE",
                "viscosity_quantifier": "FIXED_DISCRETE_POSITIVE",
                "solution_class": "DISCRETE_APPROXIMATION",
                "relation_to_endpoint": "APPROXIMATION_ONLY",
                "endpoint_branch": "NONE",
            }
        )
        experiment["residual"]["consumer_ids"] = [A_ID]
        self.registry["obligations"].append(experiment)
        a = _find(self.registry["obligations"], A_ID)
        a["dependency_mode"] = "ALL"
        a["dependencies"] = [experiment["id"]]
        self.assertInvalid("cannot realize a formal claim")


class EvidenceAndClosureTests(RegistryTestCase):
    def test_self_asserted_native_receipt_cannot_close_one_public_endpoint(self) -> None:
        evidence = _native_evidence(self.registry)
        _close_a(self.registry, evidence)
        self.assertInvalid("native receipt was not freshly revalidated")

    def test_background_native_receipt_cannot_close_claim(self) -> None:
        evidence = _native_evidence(self.registry)
        _close_a(self.registry, evidence)
        _find(self.registry["obligations"], A_ID)["evidence_links"][0]["role"] = "BACKGROUND"
        self.assertInvalid("false closure claim; fresh native receipt required")

    def test_false_closure_without_native_receipt_is_rejected(self) -> None:
        _close_a(self.registry)
        self.assertInvalid("false closure claim; fresh native receipt required")

    def test_generated_surface_snapshot_cannot_close_a_theorem(self) -> None:
        snapshot = _surface_snapshot(self.registry)
        _close_a(self.registry, snapshot)
        self.assertInvalid("false closure claim; fresh native receipt required")

    def test_experiment_receipt_cannot_be_laundered_as_realization(self) -> None:
        evidence = _experiment_evidence(self.registry)
        self.registry["evidence"].append(evidence)
        _find(self.registry["obligations"], A_ID)["evidence_links"].append(
            {"evidence_id": evidence["id"], "role": "REALIZATION"}
        )
        self.assertInvalid("experiment-as-proof laundering is forbidden")

    def test_verifier_bypass_with_non_native_receipt_is_rejected(self) -> None:
        evidence = _native_evidence(self.registry)
        verifier = _verifier(self.registry, "verifier.registry.strict")
        evidence["receipt"]["verifier_id"] = verifier["id"]
        evidence["receipt"]["command"] = verifier["command"]
        evidence["receipt"]["axioms"] = []
        _close_a(self.registry, evidence)
        self.assertInvalid("native receipt uses a non-native verifier", "closure receipt is not native")

    def test_bad_receipt_command_is_rejected(self) -> None:
        evidence = _native_evidence(self.registry)
        evidence["receipt"]["command"] = "python3 scripts/fake_success.py"
        _close_a(self.registry, evidence)
        self.assertInvalid("command does not match registered verifier")

    def test_stale_receipt_is_rejected_with_fixed_utc_clock(self) -> None:
        evidence = _native_evidence(self.registry, generated_at=NOW - timedelta(days=2))
        _close_a(self.registry, evidence)
        self.assertInvalid("stale receipt")

    def test_receipt_one_second_in_future_is_rejected(self) -> None:
        evidence = _native_evidence(self.registry)
        evidence["receipt"]["generated_at"] = (NOW + timedelta(seconds=1)).isoformat()
        _close_a(self.registry, evidence)
        self.assertInvalid("receipt is from the future")

    def test_stale_receipt_revision_is_rejected(self) -> None:
        evidence = _native_evidence(self.registry)
        evidence["receipt"]["repository_revision"] = "d" * 40
        _close_a(self.registry, evidence)
        self.assertInvalid("receipt revision must match immutable provenance source revision")

    def test_unsound_axiom_is_rejected(self) -> None:
        evidence = _native_evidence(self.registry)
        evidence["receipt"]["axioms"].append("sorryAx")
        _close_a(self.registry, evidence)
        self.assertInvalid("axiom audit contains forbidden dependencies")

    def test_failing_native_receipt_cannot_close_claim(self) -> None:
        evidence = _native_evidence(self.registry)
        evidence["receipt"]["exit_code"] = 1
        evidence["receipt"]["result"] = "FAIL"
        _close_a(self.registry, evidence)
        self.assertInvalid("failing receipt cannot close a claim")

    def test_receipt_declaration_must_match_obligation(self) -> None:
        evidence = _native_evidence(self.registry)
        evidence["receipt"]["declaration"] = "Navier.Clay.UnrelatedStatement"
        _close_a(self.registry, evidence)
        self.assertInvalid("receipt declaration does not match obligation")

    def test_receipt_and_provenance_digest_must_match(self) -> None:
        evidence = _native_evidence(self.registry)
        evidence["receipt"]["artifact_sha256"] = "e" * 64
        _close_a(self.registry, evidence)
        self.assertInvalid("receipt/provenance artifact digests differ")

    def test_falsification_without_checked_witness_is_rejected(self) -> None:
        a = _find(self.registry["obligations"], A_ID)
        a["disposition"] = "FALSIFIED"
        a["residual"] = None
        self.assertInvalid("falsified/reverted disposition requires a checked witness")

    def test_red_disposition_without_linked_falsification_witness_is_rejected(self) -> None:
        node = _find(self.registry["obligations"], "critical.unconditional_bound")
        node["disposition"] = "RED"
        self.assertInvalid("RED disposition requires a linked falsification witness")

    def test_non_falsification_evidence_cannot_witness_red_disposition(self) -> None:
        node_id = "critical.unconditional_bound"
        snapshot = _surface_snapshot(self.registry)
        snapshot["supports"] = [node_id]
        self.registry["evidence"].append(snapshot)
        node = _find(self.registry["obligations"], node_id)
        node["disposition"] = "RED"
        node["evidence_links"].append(
            {"evidence_id": snapshot["id"], "role": "FALSIFICATION"}
        )
        self.assertInvalid("RED disposition requires a linked falsification witness")

    def test_checked_falsification_witness_is_accepted(self) -> None:
        witness = _falsification_witness(self.registry)
        self.registry["evidence"].append(witness)
        a = _find(self.registry["obligations"], A_ID)
        a["disposition"] = "FALSIFIED"
        a["residual"] = None
        a["evidence_links"].append({"evidence_id": witness["id"], "role": "FALSIFICATION"})
        self.assertValid()

    def test_falsification_witness_requires_pinned_artifact(self) -> None:
        witness = _falsification_witness(self.registry)
        witness["provenance"]["artifact_sha256"] = None
        self.registry["evidence"].append(witness)
        a = _find(self.registry["obligations"], A_ID)
        a["disposition"] = "FALSIFIED"
        a["residual"] = None
        a["evidence_links"].append({"evidence_id": witness["id"], "role": "FALSIFICATION"})
        self.assertInvalid("artifact-backed evidence requires a digest")

    def test_renamed_global_closure_evasion_is_rejected(self) -> None:
        self.registry["campaign"]["global_disposition"] = "CLOSED"
        self.registry["campaign"]["scientific_status"] = "CONDITIONAL_FRONTIER"
        self.assertInvalid("false global closure claim; no public endpoint is natively closed")

    def test_cost_or_stall_verifier_age_must_be_nonnegative(self) -> None:
        _verifier(self.registry, "verifier.lean.native")["receipt_max_age_seconds"] = -1
        self.assertInvalid("receipt_max_age_seconds: expected nonnegative integer")


class ProvenanceTests(RegistryTestCase):
    def test_mutable_evidence_provenance_is_rejected(self) -> None:
        evidence = _surface_snapshot(self.registry)
        evidence["provenance"]["source_revision"] = "refs/heads/main"
        self.registry["evidence"].append(evidence)
        self.assertInvalid("mutable provenance is forbidden")

    def test_working_tree_provenance_revision_is_rejected(self) -> None:
        evidence = _surface_snapshot(self.registry)
        evidence["provenance"]["source_revision"] = "working-tree"
        self.registry["evidence"].append(evidence)
        self.assertInvalid("mutable provenance is forbidden")

    def test_future_provenance_observed_at_is_rejected(self) -> None:
        evidence = _surface_snapshot(self.registry)
        evidence["provenance"]["observed_at"] = (
            NOW + timedelta(seconds=1)
        ).isoformat()
        self.registry["evidence"].append(evidence)
        self.assertInvalid("provenance observation is from the future")

    def test_evidence_must_claim_immutable_provenance(self) -> None:
        evidence = _surface_snapshot(self.registry)
        evidence["provenance"]["immutable"] = False
        self.registry["evidence"].append(evidence)
        self.assertInvalid("evidence provenance must be immutable")

    def test_arxiv_reference_must_pin_a_version(self) -> None:
        tao = _find(self.registry["references"], "ref.tao.2019")
        tao["locator"] = "arxiv:1908.04958"
        self.assertInvalid("arXiv locators must pin a version")

    def test_mutable_reference_locator_is_rejected(self) -> None:
        self.registry["references"][0]["locator"] = "journal:navier/latest"
        self.assertInvalid("mutable locator is forbidden")

    def test_ancestor_baseline_revision_is_accepted(self) -> None:
        result = validate_registry(
            self.registry,
            now=NOW,
            repo_root=ROOT,
            check_git_revision=True,
        )
        self.assertTrue(result.valid, "\n".join(result.errors))

    def test_missing_baseline_commit_is_rejected(self) -> None:
        self.registry["base_revision"] = "f" * 40
        result = validate_registry(
            self.registry,
            now=NOW,
            repo_root=ROOT,
            check_git_revision=True,
        )
        text = "\n".join(result.errors)
        self.assertFalse(result.valid)
        self.assertIn("missing or unverifiable baseline commit", text)


class DerivedStatusAndRendererTests(RegistryTestCase):
    def test_derived_status_counts_obligations_from_registry(self) -> None:
        status = derived_status(self.registry)
        self.assertEqual(
            status["dispositions"],
            {"DECOMPOSED": 9, "RED": 1, "SCAFFOLDED": 18},
        )
        self.assertEqual(
            status["claim_tiers"],
            {
                "CONJECTURE": 9,
                "EXPERIMENT": 1,
                "FALSIFICATION": 1,
                "SCAFFOLD": 3,
                "THEOREM": 14,
            },
        )
        self.assertEqual([row["branch"] for row in status["endpoints"]], ["FEFFERMAN_A", "FEFFERMAN_C"])

    def test_derived_status_reflects_mutated_disposition_without_cached_view(self) -> None:
        _find(self.registry["obligations"], A_ID)["disposition"] = "RED"
        status = derived_status(self.registry)
        self.assertEqual(
            status["dispositions"],
            {"DECOMPOSED": 9, "RED": 2, "SCAFFOLDED": 17},
        )
        self.assertEqual(status["endpoints"][0]["disposition"], "RED")

    def test_text_renderer_names_ssot_global_status_and_residuals(self) -> None:
        rendered = _render_text(derived_status(self.registry))
        self.assertIn("derived; registry is the SSOT", rendered)
        self.assertIn("global: SCAFFOLDED / SCIENTIFIC_FRONTIER", rendered)
        self.assertIn("FEFFERMAN_A: SCAFFOLDED", rendered)
        self.assertIn(
            "residual: Construct a native theorem term inhabiting "
            "Navier.Clay.StatementA",
            rendered,
        )

    def test_text_renderer_reports_blocked_barriers_deterministically(self) -> None:
        rendered = _render_text(derived_status(self.registry))
        self.assertIn("approach.energy: DECOMPOSED", rendered)
        self.assertIn("blocked=barrier.scaling_criticality,barrier.supercritical_energy_gap,barrier.weak_strong_gap", rendered)


class SchemaDossierAndManifestTests(unittest.TestCase):
    def test_schema_is_closed_world_for_every_object_definition(self) -> None:
        schema = load_json(SCHEMA_PATH)
        objects = {"$": schema}
        objects.update(
            {
                f"$defs.{name}": definition
                for name, definition in schema["$defs"].items()
                if definition.get("type") == "object"
            }
        )
        for path, definition in objects.items():
            with self.subTest(path=path):
                self.assertIs(definition.get("additionalProperties"), False)
                self.assertEqual(set(definition.get("required", [])), set(definition.get("properties", {})))

    def test_schema_top_level_contract_exactly_matches_registry_keys(self) -> None:
        schema = load_json(SCHEMA_PATH)
        registry = load_json(REGISTRY_PATH)
        self.assertEqual(set(schema["required"]), set(schema["properties"]))
        self.assertEqual(set(schema["properties"]), set(registry))
        self.assertEqual(schema["properties"]["obligations"]["minItems"], 1)

    def test_dossier_has_exactly_routes_r1_through_r11(self) -> None:
        text = ATTACK_PATH.read_text(encoding="utf-8")
        route_numbers = re.findall(r"^### R(\d+) — .+$", text, flags=re.MULTILINE)
        self.assertEqual(route_numbers, [str(number) for number in range(1, 12)])

    def test_every_dossier_route_exposes_six_required_fields(self) -> None:
        text = ATTACK_PATH.read_text(encoding="utf-8")
        matches = list(re.finditer(r"^### R(\d+) — .+$", text, flags=re.MULTILINE))
        labels = (
            "Dependencies",
            "Deliverable",
            "First strictly lower residual",
            "Kill criterion",
            "Pivot",
            "Evidence",
        )
        for index, match in enumerate(matches):
            end = matches[index + 1].start() if index + 1 < len(matches) else text.index("\n## 6.", match.end())
            section = text[match.end():end]
            with self.subTest(route=f"R{match.group(1)}"):
                for label in labels:
                    self.assertEqual(section.count(f"**{label}:**"), 1, label)

    def test_manifest_ids_are_unique_and_entries_are_primary(self) -> None:
        manifest = load_json(MANIFEST_PATH)
        ids = [source["id"] for source in manifest["sources"]]
        self.assertEqual(len(ids), len(set(ids)))
        self.assertTrue(ids)
        for source in manifest["sources"]:
            with self.subTest(source=source["id"]):
                self.assertIs(source["primary"], True)
                self.assertTrue(source["url"].startswith("https://"))
                self.assertTrue(source["roles"])

    def test_dossier_citations_and_manifest_source_keys_have_exact_coverage(self) -> None:
        dossier = ATTACK_PATH.read_text(encoding="utf-8")
        manifest = load_json(MANIFEST_PATH)
        citation_keys = set(re.findall(r"\[([A-Z][A-Z0-9_]*[0-9]{4})\]", dossier))
        source_keys = {source["id"] for source in manifest["sources"]}
        self.assertEqual(citation_keys, source_keys)


if __name__ == "__main__":
    unittest.main()
