.PHONY: test-grd test-grd-violate
test-grd:
python3 scripts/grd_test.py --mode grd --N 8 --nmax 10 --r 2 --alpha 12.0 --beta 0.7
test-grd-violate:
python3 scripts/grd_test.py --mode violate --N 8 --nmax 10 --r 2 --R 7 --eps 1.0 --alpha 12.0 --beta 0.7
