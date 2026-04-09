import subprocess

def test_cube_product_spectrum_compare():
    p = subprocess.run(
        ["python3", "experiments/poincare/cube_product_spectrum_compare.py"],
        capture_output=True, text=True
    )
    assert p.returncode == 0, f"script failed:\n{p.stderr}"
    for line in p.stdout.strip().split("\n"):
        L, numeric_gap, analytic_gap, lower_bound, err = [float(x) for x in line.split()]
        assert analytic_gap >= lower_bound, f"analytic_gap={analytic_gap} < lower_bound={lower_bound} at L={L}"
