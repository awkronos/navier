PYTHON ?= python3

.NOTPARALLEL:
.PHONY: check proof test lean axioms adaptive-bench conditional-audit closure api-pin-census

check: closure test lean axioms

# Every Navier module must sit inside the import closure of Navier.lean or be
# an intentional standalone audit surface; otherwise whole-environment axiom
# scans silently miss it.
closure:
	$(PYTHON) tools/module-closure-check.py

proof:
	@~/.claude/scripts/open-math.py verify --project navier --report /tmp/proof-report.json --sidecar /tmp/open_math.json

# The battery is every stdlib-unittest root in this repository, declared ONCE
# here and run by `make test` (which is what the CI python job now calls).
# Measured at origin/main 80540a20c7d095876bdf69b9c52ba098f6845b64: the gate
# README.md cites for its own scope claims -- scripts/test_readme_scope_truth.py,
# 8 tests that recompute the formalization.yaml row counts and refuse a page
# that reads as though the Clay problem were settled -- sat outside the only
# root the battery discovered, so nothing scheduled and no documented command
# ever ran it. A test that no run executes pins nothing.
# tests/test_battery_schedule.py fails if a unittest test file lands in a root
# missing from this list, or if CI stops calling `make test`.
TEST_ROOTS ?= tests scripts
TEST_PATTERN ?= test_*.py

test:
	@for root in $(TEST_ROOTS); do \
		echo "== unittest discover -s $$root -p $(TEST_PATTERN)"; \
		$(PYTHON) -m unittest discover -s $$root -p $(TEST_PATTERN) -v || exit 1; \
	done

adaptive-bench:
	$(PYTHON) scripts/navier_adaptive_bench.py --case mms

conditional-audit:
	lake env lean Navier/ConditionalAudit.lean

lean:
	lake env lean Navier.lean

axioms:
	lake env lean Navier/AxiomAudit.lean
	lake env lean scripts/AuditAllAxioms.lean

# Name-by-name comparison of Navier/APIPin's pins against the compiler's own
# declaration environment (scripts/ApiEnvCensus.lean), not a grep census.
api-pin-census:
	$(PYTHON) scripts/api_pin_census.py
