"""Hostile shape tests for the observation-only experiment replay gate."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from replay_experiment import ManifestError, replay, validate_manifest  # noqa: E402


REGISTRY = json.loads((ROOT / "data" / "attack_registry.json").read_text(encoding="utf-8"))
EXPERIMENT_DOMAIN = next(
    obligation["domain"]
    for obligation in REGISTRY["obligations"]
    if obligation["id"] == "computation.intermediate_falsification"
)
SANDBOX_AVAILABLE = (
    sys.platform == "darwin"
    and Path("/usr/bin/sandbox-exec").is_file()
    and not Path("/usr/bin/sandbox-exec").is_symlink()
)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def valid_manifest() -> dict[str, object]:
    return {
        "schema_version": "navier.experiment_run@1.0.0",
        "experiment_id": "experiment.example_probe",
        "obligation_id": "computation.intermediate_falsification",
        "generated_at": "2026-07-14T18:00:00Z",
        "repository_revision": "a" * 40,
        "epistemic_status": "OBSERVATION_ONLY",
        "closes_problem_endpoint": False,
        "model": copy.deepcopy(EXPERIMENT_DOMAIN),
        "run": {
            "command": ["python3", "experiments/example_probe.py"],
            "driver_path": "experiments/example_probe.py",
            "driver_sha256": "b" * 64,
            "seed": 17,
            "precision": "binary64",
            "truncation": "8x8x8 divergence-free Fourier grid",
            "expected_exit_code": 0,
            "stdout_sha256": "c" * 64,
        },
        "artifacts": [
            {"role": "OUTPUT", "path": "artifacts/runs/example/result.json", "sha256": "d" * 64}
        ],
    }


def write_file(repo: Path, relative: str, data: bytes) -> None:
    path = repo / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def git(repo: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=repo,
        text=True,
        capture_output=True,
        check=True,
    )
    return completed.stdout.strip()


def initialize_repository(
    repo: Path,
    *,
    driver: bytes,
    input_data: bytes = b"pinned-input\n",
    preexisting_output: bytes | None = None,
    track_driver: bool = True,
) -> str:
    git(repo, "init", "-q")
    git(repo, "config", "user.name", "Replay Test")
    git(repo, "config", "user.email", "replay-test@example.invalid")
    git(repo, "config", "commit.gpgsign", "false")
    git(repo, "config", "core.hooksPath", "/dev/null")
    registry = {
        "obligations": [
            {
                "id": "computation.intermediate_falsification",
                "kind": "EXPERIMENT",
                "claim_tier": "EXPERIMENT",
                "domain": copy.deepcopy(EXPERIMENT_DOMAIN),
            }
        ]
    }
    write_file(repo, "data/attack_registry.json", json.dumps(registry).encode("utf-8"))
    write_file(repo, "artifacts/inputs/value.txt", input_data)
    write_file(repo, "experiments/example_probe.py", driver)
    if preexisting_output is not None:
        write_file(repo, "artifacts/runs/example/result.json", preexisting_output)
    git(repo, "add", "data/attack_registry.json", "artifacts/inputs/value.txt")
    if track_driver:
        git(repo, "add", "experiments/example_probe.py")
    if preexisting_output is not None:
        git(repo, "add", "artifacts/runs/example/result.json")
    git(repo, "commit", "-qm", "fixture")
    return git(repo, "rev-parse", "HEAD")


def replay_manifest(
    revision: str,
    *,
    driver: bytes,
    stdout: bytes,
    output: bytes,
    input_data: bytes = b"pinned-input\n",
) -> dict[str, object]:
    manifest = valid_manifest()
    manifest["repository_revision"] = revision
    manifest["run"]["driver_sha256"] = digest(driver)
    manifest["run"]["stdout_sha256"] = digest(stdout)
    manifest["artifacts"] = [
        {
            "role": "INPUT",
            "path": "artifacts/inputs/value.txt",
            "sha256": digest(input_data),
        },
        {
            "role": "OUTPUT",
            "path": "artifacts/runs/example/result.json",
            "sha256": digest(output),
        },
    ]
    return manifest


class ExperimentManifestTests(unittest.TestCase):
    def assertValid(self, manifest: dict[str, object]) -> None:
        validate_manifest(
            manifest,
            repo_root=ROOT,
            registry=REGISTRY,
            check_files=False,
            check_git=False,
        )

    def assertInvalid(self, manifest: dict[str, object], fragment: str) -> None:
        with self.assertRaisesRegex(ManifestError, fragment):
            self.assertValid(manifest)

    def test_canonical_observation_shape_is_valid(self) -> None:
        self.assertValid(valid_manifest())

    def test_unknown_field_is_rejected(self) -> None:
        manifest = valid_manifest()
        manifest["proof_status"] = "PROVED"
        self.assertInvalid(manifest, "unknown fields")

    def test_experiment_cannot_claim_problem_statement_closure(self) -> None:
        manifest = valid_manifest()
        manifest["closes_problem_endpoint"] = True
        self.assertInvalid(manifest, "may never close a problem endpoint")

    def test_exact_equation_laundering_is_rejected(self) -> None:
        manifest = valid_manifest()
        manifest["model"]["equation"] = "INCOMPRESSIBLE_NAVIER_STOKES"
        self.assertInvalid(manifest, "does not match the bound registry obligation")

    def test_driver_must_be_under_experiments(self) -> None:
        manifest = valid_manifest()
        manifest["run"]["driver_path"] = "scripts/render_status.py"
        manifest["run"]["command"][1] = "scripts/render_status.py"
        self.assertInvalid(manifest, "path must be under experiments/")

    def test_non_experiment_obligation_is_rejected(self) -> None:
        manifest = valid_manifest()
        manifest["obligation_id"] = "endpoint.fefferman_a"
        self.assertInvalid(manifest, "only an EXPERIMENT obligation")

    def test_cli_fails_closed_when_manifest_is_missing(self) -> None:
        completed = subprocess.run(
            [sys.executable, str(SCRIPTS / "replay_experiment.py"), "artifacts/runs/missing.json"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(completed.returncode, 1)
        self.assertIn("INVALID experiment", completed.stderr)


class ExperimentReplayIntegrationTests(unittest.TestCase):
    @unittest.skipUnless(SANDBOX_AVAILABLE, "sandbox-exec confinement is unavailable")
    def test_replay_uses_pinned_driver_and_input_in_fresh_snapshot(self) -> None:
        driver = b"""from pathlib import Path
import os

source = Path("artifacts/inputs/value.txt").read_text(encoding="utf-8").strip()
target = Path("artifacts/runs/example/result.json")
target.parent.mkdir(parents=True, exist_ok=True)
target.write_text(f"{source}:{os.environ['NAVIER_EXPERIMENT_SEED']}\\n", encoding="utf-8")
print("pinned-driver")
"""
        output = b"pinned-input:17\n"
        stdout = b"pinned-driver\n"
        with tempfile.TemporaryDirectory(prefix="navier-replay-test-") as temporary:
            repo = Path(temporary)
            revision = initialize_repository(repo, driver=driver)
            manifest = replay_manifest(
                revision,
                driver=driver,
                stdout=stdout,
                output=output,
            )
            write_file(
                repo,
                "experiments/example_probe.py",
                b"from pathlib import Path\nPath('working-tree-ran').write_text('bad')\n",
            )
            write_file(repo, "artifacts/inputs/value.txt", b"dirty-input\n")

            replay(manifest, repo_root=repo)

            self.assertFalse((repo / "working-tree-ran").exists())
            self.assertFalse((repo / "artifacts/runs/example/result.json").exists())

    def test_untracked_driver_is_rejected_before_execution(self) -> None:
        driver = b"""from pathlib import Path
Path("working-tree-ran").write_text("bad", encoding="utf-8")
"""
        with tempfile.TemporaryDirectory(prefix="navier-replay-test-") as temporary:
            repo = Path(temporary)
            revision = initialize_repository(repo, driver=driver, track_driver=False)
            manifest = replay_manifest(
                revision,
                driver=driver,
                stdout=b"",
                output=b"unused\n",
            )

            with self.assertRaisesRegex(
                ManifestError, "path is not tracked at the declared revision"
            ):
                replay(manifest, repo_root=repo)

            self.assertFalse((repo / "working-tree-ran").exists())

    def test_unsafe_argument_is_rejected(self) -> None:
        driver = b"print('unused')\n"
        with tempfile.TemporaryDirectory(prefix="navier-replay-test-") as temporary:
            repo = Path(temporary)
            revision = initialize_repository(repo, driver=driver)
            manifest = replay_manifest(
                revision,
                driver=driver,
                stdout=b"unused\n",
                output=b"unused\n",
            )
            manifest["run"]["command"].append("../../escape")

            with self.assertRaisesRegex(ManifestError, "unsafe command argument"):
                validate_manifest(manifest, repo_root=repo, check_files=False)

    @unittest.skipUnless(SANDBOX_AVAILABLE, "sandbox-exec confinement is unavailable")
    def test_undeclared_write_is_rejected(self) -> None:
        driver = b"""from pathlib import Path
target = Path("artifacts/runs/example/result.json")
target.parent.mkdir(parents=True, exist_ok=True)
target.write_bytes(b"declared\\n")
Path("artifacts/rogue.txt").write_bytes(b"rogue\\n")
print("mutated")
"""
        with tempfile.TemporaryDirectory(prefix="navier-replay-test-") as temporary:
            repo = Path(temporary)
            revision = initialize_repository(repo, driver=driver)
            manifest = replay_manifest(
                revision,
                driver=driver,
                stdout=b"mutated\n",
                output=b"declared\n",
            )

            with self.assertRaisesRegex(ManifestError, "undeclared filesystem mutation"):
                replay(manifest, repo_root=repo)

    @unittest.skipUnless(SANDBOX_AVAILABLE, "sandbox-exec confinement is unavailable")
    def test_noop_cannot_reuse_preexisting_output(self) -> None:
        driver = b"print('no-op')\n"
        output = b"preexisting\n"
        with tempfile.TemporaryDirectory(prefix="navier-replay-test-") as temporary:
            repo = Path(temporary)
            revision = initialize_repository(
                repo,
                driver=driver,
                preexisting_output=output,
            )
            manifest = replay_manifest(
                revision,
                driver=driver,
                stdout=b"no-op\n",
                output=output,
            )

            with self.assertRaisesRegex(
                ManifestError, "expected a regular non-symlink file"
            ):
                replay(manifest, repo_root=repo)

    def test_validate_only_binds_pinned_inputs_without_executing(self) -> None:
        driver = b"print('must-not-run')\n"
        output = b"recorded\n"
        with tempfile.TemporaryDirectory(prefix="navier-replay-test-") as temporary:
            repo = Path(temporary)
            revision = initialize_repository(repo, driver=driver)
            manifest = replay_manifest(
                revision,
                driver=driver,
                stdout=b"must-not-run\n",
                output=output,
            )
            write_file(repo, "artifacts/runs/example/result.json", output)
            write_file(repo, "experiments/example_probe.py", b"raise SystemExit(91)\n")
            write_file(repo, "artifacts/inputs/value.txt", b"dirty-input\n")

            validate_manifest(manifest, repo_root=repo)

            dirty_manifest = copy.deepcopy(manifest)
            dirty_manifest["artifacts"][0]["sha256"] = digest(b"dirty-input\n")
            with self.assertRaisesRegex(ManifestError, "pinned digest mismatch"):
                validate_manifest(dirty_manifest, repo_root=repo)


if __name__ == "__main__":
    unittest.main()
