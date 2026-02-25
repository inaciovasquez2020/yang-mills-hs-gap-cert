import math
import numpy as np

# BPST curvature density proxy
def F_sq(y, center, lam):
    r2 = np.sum((y - center)**2, axis=1)
    return 192.0 * lam**4 / (r2 + lam*lam)**4

def estimate_K(center_x, config, lam=1.0, nsamp=400000, sigma_mult=8.0, seed=0):
    """
    Estimates K_center_x = ∫ |F_config(y)|^2 / |y-center_x|^2 dy
    by importance sampling with y ~ N(center_x, sigma^2 I).
    Returns an uncalibrated estimate; ratios across configs are reliable.
    """
    rng = np.random.default_rng(seed)
    sigma = sigma_mult * lam
    y = rng.normal(loc=center_x, scale=sigma, size=(nsamp, 4))

    denom = np.sum((y - center_x)**2, axis=1) + 1e-12

    # build |F_total|^2 proxy from sum of bubble densities
    # proxy: (sum sqrt(F_i^2))^2 so it agrees with single bubble and is nonnegative
    roots = np.zeros(nsamp)
    for c in config:
        roots += np.sqrt(F_sq(y, c, lam))
    Ftot = roots * roots

    # proposal density p(y) for 4D Gaussian
    # p(y) = (2πσ^2)^(-2) exp(-|y-center|^2/(2σ^2))
    r2 = np.sum((y - center_x)**2, axis=1)
    p = (2*math.pi*sigma*sigma)**(-2) * np.exp(-r2/(2*sigma*sigma))

    return np.mean((Ftot / denom) / p)

def main():
    expected = 64 * math.pi**2
    lam = 1.0

    for d in [5.0, 10.0, 20.0, 40.0]:
        c0 = np.array([0.0,0.0,0.0,0.0])
        cd = np.array([d,0.0,0.0,0.0])

        single_cfg = [c0]
        two_cfg    = [c0, cd]

        # evaluate at both likely maximizers (near each bubble center)
        K0_single = estimate_K(c0, single_cfg, lam=lam, seed=1)
        K0_two    = estimate_K(c0, two_cfg,    lam=lam, seed=2)

        Kd_single = estimate_K(cd, [cd],       lam=lam, seed=3)
        Kd_two    = estimate_K(cd, two_cfg,    lam=lam, seed=4)

        # ratio-calibrate to the known single-bubble value
        K0_two_cal = (K0_two / K0_single) * expected
        Kd_two_cal = (Kd_two / Kd_single) * expected
        Kmax_cal = max(K0_two_cal, Kd_two_cal)

        print("d =", d,
              " K0/expected ≈", K0_two_cal/expected,
              " Kd/expected ≈", Kd_two_cal/expected,
              " Kmax/expected ≈", Kmax_cal/expected)

if __name__ == "__main__":
    main()
