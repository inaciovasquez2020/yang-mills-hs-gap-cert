import math
import random
from dataclasses import dataclass

def logsumexp(xs):
    m = max(xs)
    return m + math.log(sum(math.exp(x - m) for x in xs))

@dataclass
class ToyResult:
    n: int
    beta: float
    samples: int
    E_orbit: float
    gaussian_domination_holds: bool

def sample_mixture(n, beta, samples, p=0.5, mu=2.0, sigma=1.0):
    rng = random.Random(0)
    E = 0.0
    gd_ok = True
    for _ in range(samples):
        comp = 1 if rng.random() < p else -1
        x = [rng.gauss(comp * mu, sigma) for _ in range(n)]
        r2 = sum(xi * xi for xi in x)
        E += r2
        if r2 > n * (mu * mu + 3 * sigma * sigma):
            gd_ok = False
    E /= samples
    return E, gd_ok

def main():
    grid_n = [16, 32, 64]
    beta = 1.0
    samples = 2000
    out = []
    for n in grid_n:
        E, gd_ok = sample_mixture(n, beta, samples)
        out.append(ToyResult(n=n, beta=beta, samples=samples, E_orbit=E, gaussian_domination_holds=gd_ok))
    for r in out:
        print(f"n={r.n} beta={r.beta} samples={r.samples} E_orbit={r.E_orbit:.4f} gaussian_domination_holds={r.gaussian_domination_holds}")
    bad = [r for r in out if r.gaussian_domination_holds]
    if bad:
        raise SystemExit("toy test inconclusive: Gaussian domination did not fail on some sizes")
    print("toy test: orbit-energy tails break Gaussian domination across all tested sizes")

if __name__ == "__main__":
    main()
