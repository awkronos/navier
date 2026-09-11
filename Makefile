PYTHON ?= python3

.NOTPARALLEL:
.PHONY: check proof test lean axioms adaptive-bench conditional-audit closure

check: closure test lean axioms

# Every Navier module must sit inside the import closure of Navier.lean or be
# an intentional standalone audit surface; otherwise whole-environment axiom
# scans silently miss it.
closure:
	$(PYTHON) tools/module-closure-check.py

proof:
	@~/.claude/scripts/open-math.py verify --project navier --report /tmp/proof-report.json --sidecar /tmp/open_math.json

test:
	$(PYTHON) -m unittest discover -s tests -v

adaptive-bench:
	$(PYTHON) scripts/navier_adaptive_bench.py --case mms

conditional-audit:
	lake env lean Navier/ConditionalAudit.lean

lean:
	lake env lean Navier.lean

axioms:
	lake env lean Navier/AxiomAudit.lean
	lake env lean scripts/AuditAllAxioms.lean
