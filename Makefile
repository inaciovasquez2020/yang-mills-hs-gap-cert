.RECIPEPREFIX := >
.PHONY: test-grd test-grd-violate
test-grd:
python3 scripts/grd_test.py --mode grd
test-grd-violate:
python3 scripts/grd_test.py --mode violate
