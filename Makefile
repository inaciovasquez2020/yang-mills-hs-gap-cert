.PHONY: test-grd test-grd-violate
test-grd:
printf " python3 scripts/grd_test.py --mode grd\n" | sh
test-grd-violate:
printf " python3 scripts/grd_test.py --mode violate\n" | sh
