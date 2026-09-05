PYTHON ?= python3

.NOTPARALLEL:
.PHONY: check proof test lean axioms

check: test lean axioms

proof:
	@~/.claude/scripts/proof-report-refresh.sh --oneline

test:
	$(PYTHON) -m unittest discover -s tests -v

lean:
	lake env lean Navier.lean

axioms:
	lake env lean Navier/AxiomAudit.lean
