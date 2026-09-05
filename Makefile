PYTHON ?= python3

.NOTPARALLEL:
.PHONY: check proof registry test lean axioms

check: test registry lean axioms

proof:
	@~/.claude/scripts/proof-report-refresh.sh --oneline

registry:
	$(PYTHON) scripts/validate_registry.py data/attack_registry.json

test:
	$(PYTHON) -m unittest discover -s tests -v

lean:
	lake env lean Navier.lean

axioms:
	lake env lean Navier/AxiomAudit.lean
