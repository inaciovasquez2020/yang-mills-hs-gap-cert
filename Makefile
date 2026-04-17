.PHONY: verify test

verify:
	python3 scripts/check_monotonicity.py

test:
	python3 scripts/check_monotonicity.py
