PYTHON ?= python3

.NOTPARALLEL:
.PHONY: check registry test status status-json lean axioms

check: test registry status lean axioms

registry:
	$(PYTHON) scripts/validate_registry.py data/attack_registry.json

test:
	$(PYTHON) -m unittest discover -s tests -v

status:
	$(PYTHON) scripts/render_status.py data/attack_registry.json

status-json:
	$(PYTHON) scripts/render_status.py --json data/attack_registry.json

lean:
	lake build Navier

axioms:
	lake env lean Navier/AxiomAudit.lean
