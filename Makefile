.PHONY: verify test

verify:
	./scripts/verify_cert.sh certs/YM_HS_GAP_CERT_0001.json
	./scripts/verify_cert.sh certs/YM_HS_GAP_CERT_0002.json
	./scripts/verify_cert.sh certs/YM_HS_GAP_CERT_0003.json
	python3 scripts/check_monotonicity.py

test:
	./scripts/verify_cert.sh certs/YM_HS_GAP_CERT_0001.json
	python3 scripts/check_monotonicity.py
