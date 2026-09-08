PYTHON ?= python3

.NOTPARALLEL:
.PHONY: check proof test lean axioms

check: test lean axioms

proof:
	@~/.claude/scripts/open-math.py verify --project navier --report /tmp/proof-report.json --sidecar /tmp/open_math.json

test:
	$(PYTHON) -m unittest discover -s tests -v

lean:
	lake env lean Navier.lean

axioms:
	lake env lean Navier/AxiomAudit.lean
	lake env lean scripts/AuditAllAxioms.lean
