import subprocess

def test_plaquette_gap_scaling_verify():
    p = subprocess.run(
        ["python3", "experiments/gauge_space/plaquette_gap_scaling_verify.py"],
        capture_output=True, text=True
    )
    assert p.returncode == 0, f"script failed:\n{p.stderr}"
    for line in p.stdout.strip().split("\n"):
        n, numeric_gap, analytic_gap, lower_bound, err = [float(x) for x in line.split()]
        assert err <= 1e-10, f"err={err} too large at n={n}"
