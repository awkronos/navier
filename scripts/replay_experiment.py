#!/usr/bin/env python3
"""Fail-closed replay gate for Navier experiment artifacts.

The gate executes no shell text.  It accepts only a pinned Python driver under
``experiments/``, checks its digest, replays it with a fixed seed supplied in
the manifest, and compares stdout and declared artifacts byte-for-byte by
SHA-256.  Even a successful replay is explicitly observation or falsification
evidence; the manifest cannot claim a problem endpoint.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import stat
import subprocess
import sys
import tarfile
import tempfile
from datetime import datetime
from pathlib import Path, PurePosixPath
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
REGISTRY_PATH = ROOT / "data" / "attack_registry.json"
ID_RE = re.compile(r"^[a-z][a-z0-9]*(?:[._-][a-z0-9]+)+$")
SHA_RE = re.compile(r"^[0-9a-f]{64}$")
COMMIT_RE = re.compile(r"^[0-9a-f]{40}$")
SAFE_ARG_RE = re.compile(r"^-{0,2}[A-Za-z0-9_][A-Za-z0-9_.:=+@,-]*$")
SANDBOX_EXEC = Path("/usr/bin/sandbox-exec")


class ManifestError(ValueError):
    """An experiment manifest violates the replay contract."""


def _object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ManifestError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_manifest(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_object_pairs)
    except (OSError, json.JSONDecodeError) as error:
        raise ManifestError(str(error)) from error
    if not isinstance(value, dict):
        raise ManifestError("$: expected an object")
    return value


def _exact_object(value: Any, keys: set[str], path: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise ManifestError(f"{path}: expected an object")
    missing = sorted(keys - set(value))
    unknown = sorted(set(value) - keys)
    if missing:
        raise ManifestError(
            f"{path}: missing {', '.join(missing)}; missing fields {missing}"
        )
    if unknown:
        raise ManifestError(f"{path}: unknown fields {unknown}")
    return value


def _string(value: Any, path: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ManifestError(f"{path}: expected a nonempty string")
    return value


def _sha(value: Any, path: str) -> str:
    text = _string(value, path)
    if not SHA_RE.fullmatch(text):
        raise ManifestError(f"{path}: expected a lowercase SHA-256 digest")
    return text


def _repo_relative(value: Any, path: str, prefix: str) -> str:
    text = _string(value, path)
    if "\\" in text or any(ord(character) < 32 for character in text):
        raise ManifestError(f"{path}: path must use safe repository-relative syntax")
    relative = PurePosixPath(text)
    if (
        relative.is_absolute()
        or any(part in {"", ".", ".."} for part in relative.parts)
        or relative.as_posix() != text
    ):
        raise ManifestError(f"{path}: path must be canonical and repository-relative")
    if len(relative.parts) < 2 or relative.parts[0] != prefix:
        raise ManifestError(f"{path}: path must be under {prefix}/")
    return relative.as_posix()


def _repo_path(value: Any, path: str, repo_root: Path, prefix: str) -> Path:
    relative = _repo_relative(value, path, prefix)
    root = repo_root.resolve()
    resolved = root.joinpath(*PurePosixPath(relative).parts).resolve()
    try:
        resolved.relative_to(root)
    except ValueError as error:
        raise ManifestError(f"{path}: path escapes the repository") from error
    return resolved


def _digest(path: Path) -> str:
    hasher = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            hasher.update(block)
    return hasher.hexdigest()


def _check_file(path: Path, expected: str, label: str) -> None:
    if not path.is_file() or path.is_symlink():
        raise ManifestError(f"{label}: expected a regular non-symlink file")
    actual = _digest(path)
    if actual != expected:
        raise ManifestError(f"{label}: digest mismatch; expected {expected}, got {actual}")


def _git(repo_root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        text=True,
        capture_output=True,
        check=False,
    )


def _git_bytes(repo_root: Path, *args: str) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        ["git", *args],
        cwd=repo_root,
        capture_output=True,
        check=False,
    )


def _tracked_blob(
    repo_root: Path,
    revision: str,
    relative: str,
    expected_sha: str,
    label: str,
) -> None:
    listing = _git_bytes(repo_root, "ls-tree", "-z", revision, "--", relative)
    records = [record for record in listing.stdout.split(b"\0") if record]
    if listing.returncode != 0 or len(records) != 1:
        subject = "driver" if label == "$.run.driver_path" else "INPUT"
        raise ManifestError(
            f"{label}: {subject} is not tracked at repository revision; "
            "path is not tracked at the declared revision"
        )
    metadata, separator, raw_path = records[0].partition(b"\t")
    try:
        mode, object_type, object_id = metadata.decode("ascii").split()
    except (UnicodeDecodeError, ValueError) as error:
        raise ManifestError(f"{label}: invalid Git tree entry") from error
    if not separator or raw_path != os.fsencode(relative):
        raise ManifestError(f"{label}: path is not tracked exactly at the declared revision")
    if mode not in {"100644", "100755"} or object_type != "blob":
        raise ManifestError(f"{label}: tracked entry must be a regular file")
    blob = _git_bytes(repo_root, "cat-file", "blob", object_id)
    if blob.returncode != 0:
        raise ManifestError(f"{label}: tracked bytes are unavailable")
    actual = hashlib.sha256(blob.stdout).hexdigest()
    if actual != expected_sha:
        raise ManifestError(
            f"{label}: pinned digest mismatch; expected {expected_sha}, got {actual}"
        )


def _safe_command_argument(argument: str, index: int) -> None:
    if (
        len(argument) > 256
        or "/" in argument
        or "\\" in argument
        or ".." in argument
        or Path(argument).is_absolute()
        or not SAFE_ARG_RE.fullmatch(argument)
    ):
        raise ManifestError(
            f"$.run.command[{index}]: unsafe repository path argument; "
            "unsafe command argument"
        )


def _load_registry(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_object_pairs)
    except (OSError, json.JSONDecodeError) as error:
        raise ManifestError(f"registry: {error}") from error
    if not isinstance(value, dict):
        raise ManifestError("registry: expected an object")
    return value


def validate_manifest(
    manifest: dict[str, Any],
    *,
    repo_root: Path = ROOT,
    registry: dict[str, Any] | None = None,
    check_files: bool = True,
    check_git: bool = True,
) -> dict[str, Any]:
    """Validate a manifest and return its bound registry obligation."""

    keys = {
        "schema_version",
        "experiment_id",
        "obligation_id",
        "generated_at",
        "repository_revision",
        "epistemic_status",
        "closes_problem_endpoint",
        "model",
        "run",
        "artifacts",
    }
    data = _exact_object(manifest, keys, "$")
    if data["schema_version"] != "navier.experiment_run@1.0.0":
        raise ManifestError("$.schema_version: expected 'navier.experiment_run@1.0.0'")

    experiment_id = _string(data["experiment_id"], "$.experiment_id")
    if not ID_RE.fullmatch(experiment_id):
        raise ManifestError("$.experiment_id: expected a stable lowercase identifier")
    obligation_id = _string(data["obligation_id"], "$.obligation_id")
    if not ID_RE.fullmatch(obligation_id):
        raise ManifestError("$.obligation_id: expected a stable lowercase identifier")

    generated_at = _string(data["generated_at"], "$.generated_at")
    try:
        parsed_time = datetime.fromisoformat(generated_at.replace("Z", "+00:00"))
    except ValueError as error:
        raise ManifestError("$.generated_at: expected an ISO-8601 timestamp") from error
    if parsed_time.tzinfo is None or not generated_at.endswith("Z"):
        raise ManifestError("$.generated_at: expected an explicit UTC Z timestamp")

    revision = _string(data["repository_revision"], "$.repository_revision")
    if not COMMIT_RE.fullmatch(revision):
        raise ManifestError("$.repository_revision: expected a full lowercase Git commit")
    if data["epistemic_status"] not in {"OBSERVATION_ONLY", "FALSIFICATION_WITNESS"}:
        raise ManifestError("$.epistemic_status: expected observation or falsification evidence")
    if data["closes_problem_endpoint"] is not False:
        raise ManifestError("$.closes_problem_endpoint: experiments may never close a problem endpoint")

    model_keys = {
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
    model = _exact_object(data["model"], model_keys, "$.model")
    if model["relation_to_endpoint"] != "APPROXIMATION_ONLY":
        raise ManifestError("$.model.relation_to_endpoint: experiment must remain APPROXIMATION_ONLY")

    registry_data = registry if registry is not None else _load_registry(repo_root / REGISTRY_PATH.relative_to(ROOT))
    obligations = registry_data.get("obligations")
    if not isinstance(obligations, list):
        raise ManifestError("registry: obligations must be a list")
    obligation = next(
        (item for item in obligations if isinstance(item, dict) and item.get("id") == obligation_id),
        None,
    )
    if obligation is None:
        raise ManifestError(f"$.obligation_id: unknown registry obligation {obligation_id!r}")
    if obligation.get("kind") != "EXPERIMENT" or obligation.get("claim_tier") != "EXPERIMENT":
        raise ManifestError("$.obligation_id: replay receipts may bind only an EXPERIMENT obligation")
    domain = obligation.get("domain")
    if not isinstance(domain, dict):
        raise ManifestError("registry obligation: missing domain")
    for field in sorted(model_keys):
        if model.get(field) != domain.get(field):
            raise ManifestError(f"$.model.{field}: does not match the bound registry obligation")

    run_keys = {
        "command",
        "driver_path",
        "driver_sha256",
        "seed",
        "precision",
        "truncation",
        "expected_exit_code",
        "stdout_sha256",
    }
    run = _exact_object(data["run"], run_keys, "$.run")
    command = run["command"]
    if not isinstance(command, list) or len(command) < 2 or not all(isinstance(arg, str) and arg for arg in command):
        raise ManifestError("$.run.command: expected a nonempty argv string array")
    if len(command) > 64:
        raise ManifestError("$.run.command: too many arguments")
    driver_relative = _repo_relative(run["driver_path"], "$.run.driver_path", "experiments")
    _repo_path(run["driver_path"], "$.run.driver_path", repo_root, "experiments")
    if command[0] != "python3" or command[1] != driver_relative:
        raise ManifestError("$.run.command: must invoke the declared driver as `python3 experiments/...`")
    for index, argument in enumerate(command[2:], start=2):
        _safe_command_argument(argument, index)
    driver_sha = _sha(run["driver_sha256"], "$.run.driver_sha256")
    if not isinstance(run["seed"], int) or isinstance(run["seed"], bool):
        raise ManifestError("$.run.seed: expected an integer")
    _string(run["precision"], "$.run.precision")
    _string(run["truncation"], "$.run.truncation")
    if run["expected_exit_code"] != 0:
        raise ManifestError("$.run.expected_exit_code: successful replay must require exit code 0")
    _sha(run["stdout_sha256"], "$.run.stdout_sha256")

    artifacts = data["artifacts"]
    if not isinstance(artifacts, list) or not artifacts:
        raise ManifestError("$.artifacts: expected at least one declared artifact")
    seen_paths: set[str] = set()
    has_output = False
    checked_artifacts: list[tuple[str, Path, str, str]] = []
    for index, raw in enumerate(artifacts):
        artifact = _exact_object(raw, {"role", "path", "sha256"}, f"$.artifacts[{index}]")
        role = artifact["role"]
        if role not in {"INPUT", "OUTPUT"}:
            raise ManifestError(f"$.artifacts[{index}].role: expected INPUT or OUTPUT")
        has_output = has_output or role == "OUTPUT"
        relative = _repo_relative(
            artifact["path"], f"$.artifacts[{index}].path", "artifacts"
        )
        artifact_path = _repo_path(artifact["path"], f"$.artifacts[{index}].path", repo_root, "artifacts")
        if relative in seen_paths:
            raise ManifestError(f"$.artifacts[{index}].path: duplicate artifact path")
        if any(
            relative.startswith(f"{seen}/") or seen.startswith(f"{relative}/")
            for seen in seen_paths
        ):
            raise ManifestError(f"$.artifacts[{index}].path: artifact paths may not overlap")
        seen_paths.add(relative)
        checked_artifacts.append(
            (
                relative,
                artifact_path,
                _sha(artifact["sha256"], f"$.artifacts[{index}].sha256"),
                role,
            )
        )
    if not has_output:
        raise ManifestError("$.artifacts: at least one OUTPUT artifact is required")

    if check_git:
        exists = _git(repo_root, "cat-file", "-e", f"{revision}^{{commit}}")
        if exists.returncode != 0:
            raise ManifestError("$.repository_revision: missing or unverifiable commit")
        ancestor = _git(repo_root, "merge-base", "--is-ancestor", revision, "HEAD")
        if ancestor.returncode != 0:
            raise ManifestError("$.repository_revision: commit is not an ancestor of HEAD")
        _tracked_blob(
            repo_root,
            revision,
            driver_relative,
            driver_sha,
            "$.run.driver_path",
        )
        for relative, _artifact_path, expected, role in checked_artifacts:
            if role == "INPUT":
                _tracked_blob(
                    repo_root,
                    revision,
                    relative,
                    expected,
                    relative,
                )
    if check_files:
        for relative, artifact_path, expected, role in checked_artifacts:
            if role == "OUTPUT":
                _check_file(artifact_path, expected, relative)

    return obligation


def _archive_path(name: str) -> str:
    if "\\" in name or any(ord(character) < 32 for character in name):
        raise ManifestError("Git snapshot contains an unsafe path")
    relative = PurePosixPath(name)
    if (
        not relative.parts
        or relative.is_absolute()
        or any(part in {"", ".", ".."} for part in relative.parts)
        or relative.as_posix() != name
    ):
        raise ManifestError("Git snapshot contains a non-canonical path")
    return relative.as_posix()


def _excluded_from_snapshot(relative: str, outputs: set[str]) -> bool:
    return any(relative == output or relative.startswith(f"{output}/") for output in outputs)


def _extract_snapshot(
    repo_root: Path,
    revision: str,
    destination: Path,
    outputs: set[str],
) -> None:
    archived = _git_bytes(repo_root, "archive", "--format=tar", revision)
    if archived.returncode != 0:
        raise ManifestError("$.repository_revision: unable to archive the declared revision")
    destination.mkdir(mode=0o700)
    seen: set[str] = set()
    try:
        archive = tarfile.open(fileobj=io.BytesIO(archived.stdout), mode="r:")
        with archive:
            for member in archive:
                relative = _archive_path(member.name)
                if relative in seen:
                    raise ManifestError("Git snapshot contains duplicate paths")
                seen.add(relative)
                if _excluded_from_snapshot(relative, outputs):
                    continue
                target = destination.joinpath(*PurePosixPath(relative).parts)
                if member.isdir():
                    if target.exists() and not target.is_dir():
                        raise ManifestError("Git snapshot has conflicting path types")
                    target.mkdir(parents=True, exist_ok=True)
                    os.chmod(target, member.mode & 0o777)
                    continue
                if not member.isfile():
                    raise ManifestError("Git snapshot contains a non-regular entry")
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.exists() or target.is_symlink():
                    raise ManifestError("Git snapshot has conflicting file paths")
                source = archive.extractfile(member)
                if source is None:
                    raise ManifestError("Git snapshot file bytes are unavailable")
                with source, target.open("xb") as handle:
                    for block in iter(lambda: source.read(1024 * 1024), b""):
                        handle.write(block)
                os.chmod(target, member.mode & 0o777)
    except (OSError, tarfile.TarError) as error:
        raise ManifestError(f"Git snapshot extraction failed: {error}") from error


def _filesystem_state(root: Path) -> dict[str, tuple[str, int, str]]:
    state: dict[str, tuple[str, int, str]] = {}
    pending = [root]
    try:
        while pending:
            directory = pending.pop()
            with os.scandir(directory) as entries:
                for entry in entries:
                    path = Path(entry.path)
                    relative = path.relative_to(root).as_posix()
                    metadata = entry.stat(follow_symlinks=False)
                    mode = stat.S_IMODE(metadata.st_mode)
                    if stat.S_ISDIR(metadata.st_mode):
                        state[relative] = ("directory", mode, "")
                        pending.append(path)
                    elif stat.S_ISREG(metadata.st_mode):
                        state[relative] = ("file", mode, _digest(path))
                    elif stat.S_ISLNK(metadata.st_mode):
                        state[relative] = ("symlink", mode, os.readlink(path))
                    else:
                        state[relative] = ("special", mode, "")
    except OSError as error:
        raise ManifestError(f"snapshot inspection failed: {error}") from error
    return state


def _assert_only_outputs_changed(
    before: dict[str, tuple[str, int, str]],
    after: dict[str, tuple[str, int, str]],
    outputs: set[str],
) -> None:
    output_parents: set[str] = set()
    for output in outputs:
        output_parents.update(
            parent.as_posix()
            for parent in PurePosixPath(output).parents
            if parent.as_posix() != "."
        )
    for relative in sorted(set(before) | set(after)):
        if relative in outputs:
            continue
        if relative in output_parents and relative not in before:
            if after.get(relative, (None, 0, ""))[0] == "directory":
                continue
        if before.get(relative) != after.get(relative):
            raise ManifestError(
                f"$.run.command: undeclared filesystem output at {relative!r}; "
                "undeclared filesystem mutation"
            )


def _sandbox_profile(snapshot: Path) -> str:
    quoted_snapshot = json.dumps(str(snapshot.resolve()))
    return "\n".join(
        [
            "(version 1)",
            "(deny default)",
            "(allow process*)",
            "(allow file-read*)",
            "(allow sysctl-read)",
            "(allow mach-lookup)",
            f"(allow file-write* (subpath {quoted_snapshot}))",
        ]
    )


def replay(manifest: dict[str, Any], *, repo_root: Path = ROOT) -> None:
    """Replay only the pinned Git tree in a fresh, write-confined snapshot."""

    validate_manifest(manifest, repo_root=repo_root, check_files=False, check_git=True)
    if (
        not SANDBOX_EXEC.is_file()
        or SANDBOX_EXEC.is_symlink()
        or not os.access(SANDBOX_EXEC, os.X_OK)
    ):
        raise ManifestError(
            "$.run.command: supported /usr/bin/sandbox-exec confinement is unavailable"
        )

    run = manifest["run"]
    revision = manifest["repository_revision"]
    driver_relative = _repo_relative(
        run["driver_path"], "$.run.driver_path", "experiments"
    )
    inputs: list[tuple[str, str, int]] = []
    outputs: list[tuple[str, str, int]] = []
    for index, artifact in enumerate(manifest["artifacts"]):
        relative = _repo_relative(
            artifact["path"], f"$.artifacts[{index}].path", "artifacts"
        )
        target = outputs if artifact["role"] == "OUTPUT" else inputs
        target.append((relative, artifact["sha256"], index))
    output_paths = {relative for relative, _digest_value, _index in outputs}

    with tempfile.TemporaryDirectory(prefix="navier-replay-") as temporary:
        snapshot = Path(temporary) / "snapshot"
        _extract_snapshot(repo_root, revision, snapshot, output_paths)
        _check_file(
            snapshot.joinpath(*PurePosixPath(driver_relative).parts),
            run["driver_sha256"],
            "$.run.driver_path",
        )
        for relative, expected, index in inputs:
            _check_file(
                snapshot.joinpath(*PurePosixPath(relative).parts),
                expected,
                f"$.artifacts[{index}]",
            )
        before = _filesystem_state(snapshot)
        environment = {
            "LANG": "C",
            "LC_ALL": "C",
            "NAVIER_EXPERIMENT_SEED": str(run["seed"]),
            "PATH": "/usr/bin:/bin",
            "PYTHONDONTWRITEBYTECODE": "1",
            "PYTHONHASHSEED": str(run["seed"]),
            "PYTHONNOUSERSITE": "1",
            "PYTHONSAFEPATH": "1",
        }
        command = [
            str(SANDBOX_EXEC),
            "-p",
            _sandbox_profile(snapshot),
            str(Path(sys.executable).resolve()),
            driver_relative,
            *run["command"][2:],
        ]
        try:
            completed = subprocess.run(
                command,
                cwd=snapshot,
                env=environment,
                capture_output=True,
                check=False,
                timeout=300,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise ManifestError(f"$.run.command: replay failed: {error}") from error
        if completed.returncode != run["expected_exit_code"]:
            raise ManifestError(
                f"$.run.command: exit code {completed.returncode}, "
                f"expected {run['expected_exit_code']}"
            )
        stdout_digest = hashlib.sha256(completed.stdout).hexdigest()
        if stdout_digest != run["stdout_sha256"]:
            raise ManifestError(
                f"$.run.stdout_sha256: digest mismatch; expected {run['stdout_sha256']}, "
                f"got {stdout_digest}"
            )
        after = _filesystem_state(snapshot)
        _assert_only_outputs_changed(before, after, output_paths)
        for relative, expected, index in outputs:
            output_path = snapshot.joinpath(*PurePosixPath(relative).parts)
            if not output_path.is_file() or output_path.is_symlink():
                raise ManifestError(
                    f"$.artifacts[{index}]: OUTPUT must be freshly produced; "
                    "expected a regular non-symlink file"
                )
            _check_file(output_path, expected, f"$.artifacts[{index}]")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", type=Path)
    parser.add_argument(
        "--validate-only",
        action="store_true",
        help="validate an already replayed artifact without executing its driver",
    )
    args = parser.parse_args(argv)
    try:
        manifest = load_manifest(args.manifest)
        if args.validate_only:
            validate_manifest(manifest)
        else:
            replay(manifest)
    except ManifestError as error:
        print(f"INVALID experiment: {error}", file=sys.stderr)
        return 1
    print(
        f"VALID experiment={manifest['experiment_id']} status={manifest['epistemic_status']} "
        "closes_problem_endpoint=false"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
