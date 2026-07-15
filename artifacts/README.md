# Experiment artifacts

Only deterministic, replayable route-falsification artifacts belong here.
They are observation evidence, never theorem evidence.

An experiment manifest must use schema version
`navier.experiment_run@1.0.0`, bind the exact
`computation.intermediate_falsification` registry obligation, pin the Git
revision and Python driver hash, state its seed/precision/truncation, and list
the SHA-256 digest of every input and output. The driver must live under
`experiments/`; data artifacts must live under `artifacts/`. Both the driver
and every input must be regular files tracked at the declared commit. Replay
extracts that commit into a fresh snapshot with all declared outputs omitted,
runs a fixed Python argv under macOS `sandbox-exec` with writes confined to the
snapshot and networking denied, rejects every undeclared filesystem mutation,
and requires each declared output to be freshly created with its pinned digest.
The gate rejects unknown fields, shell commands, unsafe path arguments, model
drift, untracked or mutable inputs, digest drift, pre-existing-output reuse, and
any claim to close a Clay endpoint. If supported confinement is unavailable,
execution fails closed.

Replay a delivered manifest with:

```bash
python3 scripts/replay_experiment.py artifacts/runs/experiment.json
```

The first delivered run is [`runs/experiment.json`](runs/experiment.json),
with exact output in
[`runs/exact_symmetrized_triad_scan.json`](runs/exact_symmetrized_triad_scan.json).
It replays the finite symmetrized-triad scan using integer/rational arithmetic,
records both the cancelled old witness and the surviving unequal-shell/leakage
observations, and declares `closes=false` with outcome
`FALSIFICATION_WITNESS`. It is not numerical evidence for regularity or
breakdown.
