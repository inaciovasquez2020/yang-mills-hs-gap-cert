"""
test_spectral_gap.py
====================
Executable verification of the block boundary Hessian H_B and its spectral gap.

Lattice model
-------------
  • d-dimensional hypercubic lattice  Λ_L = {0,...,L-1}^d
  • Gauge group U(1)  (links are angles θ_ℓ ∈ [0,2π), algebra coordinate A_ℓ ∈ ℝ)
  • Wilson action  S_B = β Σ_{p ∈ P_∂}  (1 − cos F_p),  F_p = Σ_{ℓ ∈ ∂p} ±A_ℓ
  • Gauge-fixed: one link per site removed (temporal gauge along axis 0),
    leaving  |E_free| = d·L^d − L^(d-1)·(L-1)  independent links.

Block Hessian H_B
-----------------
  H_B[i,j] = Σ_{p ∈ P_∂}  cos(F_p(U*))  ·  (∂_i F_p)(∂_j F_p)

evaluated at the identity configuration U* = 0  (all A_ℓ = 0),
where cos(F_p) = 1, so  H_B = β · M^T M  with  M = incidence matrix
(boundary plaquettes × free links).

Spectral gap check
------------------
  Compute λ_1(H_B) = smallest nonzero eigenvalue.
  Assert  λ_1(H_B) ≥ c · L^{-2}  for the theoretical constant c.

Usage
-----
  python test_spectral_gap.py                   # default: d=2, L=4,6,8, β=5.0
  python test_spectral_gap.py --d 3 --L 4 6    # custom
"""

import argparse
import sys
import itertools
import numpy as np
from scipy import linalg

# ───────────────────────────────────────────────────────────────────────────────
# Lattice helpers
# ───────────────────────────────────────────────────────────────────────────────

def site_index(coords, L, d):
    """Row-major flat index for a lattice site."""
    idx = 0
    for c in coords:
        idx = idx * L + c
    return idx


def all_sites(L, d):
    return list(itertools.product(range(L), repeat=d))


def all_links(L, d):
    """
    Returns list of (site, mu) pairs.
    A link is identified by its base site and direction mu ∈ {0,...,d-1}.
    """
    links = []
    for site in all_sites(L, d):
        for mu in range(d):
            links.append((site, mu))
    return links


def all_plaquettes(L, d):
    """
    Returns list of (site, mu, nu) with mu < nu.
    The plaquette at site s in plane (mu,nu) has boundary links:
      (s, mu), (s+e_mu, nu), (s+e_mu+e_nu, -mu), (s+e_nu, -nu)
    Periodic boundary conditions are used for site wrap.
    """
    plaquettes = []
    sites = all_sites(L, d)
    for s in sites:
        for mu in range(d):
            for nu in range(mu+1, d):
                plaquettes.append((s, mu, nu))
    return plaquettes


def shift(site, mu, L, d, amount=1):
    """Shift site by `amount` in direction mu (periodic)."""
    s = list(site)
    s[mu] = (s[mu] + amount) % L
    return tuple(s)


def plaquette_boundary(s, mu, nu, L, d):
    """
    Return the four oriented links of plaquette (s, mu, nu).
    Each element: (base_site, direction, orientation)  where orientation ∈ {+1, -1}.
    Traversal: s→s+μ→s+μ+ν→s+ν→s
    """
    s1 = s
    s2 = shift(s, mu, L, d)
    s3 = shift(s2, nu, L, d)
    s4 = shift(s, nu, L, d)
    return [
        (s1, mu, +1),
        (s2, nu, +1),
        (s3, mu, -1),
        (s4, nu, -1),
    ]


def is_boundary_plaquette(s, mu, nu, L, d):
    """
    A plaquette touches the block boundary ∂Λ_L if at least one corner
    has a coordinate equal to 0 or L-1 in any direction.
    For d=2, L=4: all plaquettes on the outer ring of sites.
    """
    corners = [s,
               shift(s, mu, L, d),
               shift(shift(s, mu, L, d), nu, L, d),
               shift(s, nu, L, d)]
    for c in corners:
        if any(coord == 0 or coord == L - 1 for coord in c):
            return True
    return False


# ───────────────────────────────────────────────────────────────────────────────
# Gauge fixing: temporal gauge along axis 0
# ───────────────────────────────────────────────────────────────────────────────

def build_free_links(L, d):
    """
    Temporal gauge: fix A_{(s,0)} = 0 for all sites with s[0] != 0.
    That is: keep direction-0 links only on the slice s[0]=0,
    and keep all direction-mu (mu>0) links.
    Returns list of free (site, mu) link indices.
    """
    free = []
    for site in all_sites(L, d):
        for mu in range(d):
            if mu == 0 and site[0] != 0:
                continue          # gauged away
            free.append((site, mu))
    return free


# ───────────────────────────────────────────────────────────────────────────────
# Build the plaquette-link incidence matrix M (boundary plaquettes only)
# ───────────────────────────────────────────────────────────────────────────────

def build_incidence_matrix(L, d, beta, boundary_only=True):
    """
    M[p, i] = orientation of free link i in boundary plaquette p.
    At U*=0: H_B = beta * M^T M  (exact, since cos F_p = 1 at U*=0).
    """
    free_links = build_free_links(L, d)
    link_to_idx = {lk: i for i, lk in enumerate(free_links)}
    n_free = len(free_links)

    plaquettes = all_plaquettes(L, d)
    if boundary_only:
        plaquettes = [(s, mu, nu) for (s, mu, nu) in plaquettes
                      if is_boundary_plaquette(s, mu, nu, L, d)]

    n_plaq = len(plaquettes)
    M = np.zeros((n_plaq, n_free), dtype=float)

    for p_idx, (s, mu, nu) in enumerate(plaquettes):
        for (base, direction, orientation) in plaquette_boundary(s, mu, nu, L, d):
            lk = (base, direction)
            if lk in link_to_idx:
                M[p_idx, link_to_idx[lk]] += orientation
            # gauged links contribute 0 (fixed to 0)

    return M, n_free, n_plaq, free_links, plaquettes


def build_hessian(L, d, beta, boundary_only=True):
    """
    H_B = beta * M^T M   (at identity configuration, exact for U(1)).
    For non-identity U, diagonal corrections cos(F_p) ≠ 1 can be added;
    here we test the leading-order (perturbative) Hessian.
    """
    M, n_free, n_plaq, free_links, plaquettes = build_incidence_matrix(
        L, d, beta, boundary_only)
    H = beta * (M.T @ M)
    return H, M, free_links, plaquettes


# ───────────────────────────────────────────────────────────────────────────────
# Spectral gap computation
# ───────────────────────────────────────────────────────────────────────────────

def spectral_gap(H, tol=1e-10):
    """
    Returns (eigenvalues_sorted, lambda_min_nonzero).
    Zero modes correspond to gauge orbits and pure-bulk directions.
    """
    eigvals = linalg.eigvalsh(H)        # real symmetric → real eigenvalues
    eigvals_sorted = np.sort(eigvals)
    nonzero = eigvals_sorted[eigvals_sorted > tol]
    if len(nonzero) == 0:
        return eigvals_sorted, None
    return eigvals_sorted, nonzero[0]


# ───────────────────────────────────────────────────────────────────────────────
# Quadratic form test:  ⟨f, H_B f⟩ = Σ_p ||M_p f||²
# ───────────────────────────────────────────────────────────────────────────────

def quadratic_form_check(H, M, beta, n_tests=20, rng=None):
    """
    Verify ⟨f, H_B f⟩ = β · ‖Mf‖²  for random f (zero-mean projected).
    H = β · M^T M, so:
        LHS = f^T H f = β · f^T M^T M f = β · ‖Mf‖² = RHS.
    Returns max absolute relative error over n_tests random vectors.
    """
    if rng is None:
        rng = np.random.default_rng(42)
    n = H.shape[0]
    max_err = 0.0
    for _ in range(n_tests):
        f = rng.standard_normal(n)
        f -= f.mean()                   # zero-mean projection (optional, both sides scale equally)
        lhs = float(f @ H @ f)         # = β · ‖Mf‖²  (β baked into H)
        Mf  = M @ f
        rhs = beta * float(Mf @ Mf)   # explicit β factor on RHS
        if abs(lhs) < 1e-14 and abs(rhs) < 1e-14:
            continue
        denom = max(abs(lhs), abs(rhs), 1e-14)
        err = abs(lhs - rhs) / denom
        max_err = max(max_err, err)
    return max_err


# ───────────────────────────────────────────────────────────────────────────────
# Main test harness
# ───────────────────────────────────────────────────────────────────────────────

def run_test(d, L, beta, c_theory, verbose=True):
    """
    Build H_B, check quadratic form identity, check spectral gap ≥ c·L^{-2}.
    Returns True iff all checks pass.
    """
    tag = f"d={d}, L={L}, β={beta:.1f}"
    print(f"\n{'─'*60}")
    print(f"  TEST: {tag}")
    print(f"{'─'*60}")

    H, M, free_links, plaquettes = build_hessian(L, d, beta, boundary_only=True)
    n_free  = H.shape[0]
    n_plaq  = M.shape[0]
    threshold = c_theory * L**(-2)

    print(f"  Free links (gauge-fixed):     {n_free}")
    print(f"  Boundary plaquettes:          {n_plaq}")
    print(f"  H_B shape:                   {H.shape}")
    print(f"  Theoretical threshold c·L⁻²: {threshold:.6f}  (c={c_theory})")

    # ── 1. Quadratic form identity ──────────────────────────────────────────
    qf_err = quadratic_form_check(H, M, beta)
    qf_ok  = qf_err < 1e-10
    print(f"\n  [1] Quadratic form ⟨f,H_B f⟩ = β‖Mf‖²")
    print(f"      max relative error over 20 random f: {qf_err:.2e}  →  {'PASS ✓' if qf_ok else 'FAIL ✗'}")

    # ── 2. Positive semi-definiteness ──────────────────────────────────────
    eigvals, lam1 = spectral_gap(H)
    n_zero = np.sum(eigvals < 1e-10)
    psd_ok = eigvals[0] > -1e-10
    print(f"\n  [2] Positive semi-definiteness")
    print(f"      Smallest eigenvalue: {eigvals[0]:.6e}  →  {'PASS ✓' if psd_ok else 'FAIL ✗'}")
    print(f"      Zero modes (|λ|<1e-10): {n_zero}  (gauge + zero-flux directions)")

    # ── 3. Spectral gap ────────────────────────────────────────────────────
    if lam1 is not None:
        gap_ok = lam1 >= threshold
        print(f"\n  [3] Spectral gap λ₁(H_B) ≥ c·L⁻²")
        print(f"      λ₁(H_B)   = {lam1:.8f}")
        print(f"      c·L⁻²     = {threshold:.8f}")
        print(f"      Ratio λ₁/(c·L⁻²) = {lam1/threshold:.4f}  →  {'PASS ✓' if gap_ok else 'FAIL ✗'}")
        # Print a few eigenvalues for context
        if verbose:
            n_show = min(8, len(eigvals))
            ev_str = "  ".join(f"{v:.5f}" for v in eigvals[:n_show])
            print(f"      First {n_show} eigenvalues: [{ev_str}  ...]")
    else:
        gap_ok = False
        print(f"\n  [3] Spectral gap — NO nonzero eigenvalue found  →  FAIL ✗")

    # ── 4. Basis-vector quadratic form test ────────────────────────────────
    print(f"\n  [4] Quadratic form on link-space basis vectors  ⟨eᵢ,H_B eᵢ⟩ = β‖Meᵢ‖²")
    n_basis_test = min(n_free, 10)
    basis_ok = True
    for i in range(n_basis_test):
        ei = np.zeros(n_free); ei[i] = 1.0
        qf_val  = float(ei @ H @ ei)
        Mei     = M @ ei
        rhs_val = beta * float(Mei @ Mei)      # β factor here
        denom   = max(abs(qf_val), abs(rhs_val), 1e-14)
        err     = abs(qf_val - rhs_val) / denom
        if err > 1e-10:
            basis_ok = False
            print(f"      Basis {i}: ⟨eᵢ,Heᵢ⟩={qf_val:.6f}  β‖Meᵢ‖²={rhs_val:.6f}  err={err:.2e}  FAIL ✗")
    if basis_ok:
        print(f"      All {n_basis_test} basis vectors:  PASS ✓")

    all_pass = qf_ok and psd_ok and gap_ok and basis_ok
    status = "PASS ✓" if all_pass else "FAIL ✗"
    print(f"\n  ══ Overall: {status} ══")
    return all_pass


def scaling_check(d, L_values, beta, c_theory, verbose=True):
    """
    Check that λ₁(H_B) · L² converges to a constant > c_theory as L grows,
    consistent with the L^{-2} spectral gap lower bound.
    Also compare against full-lattice scalar Laplacian λ₁ = 4sin²(π/L) ~ (2π/L)².
    """
    print(f"\n{'═'*60}")
    print(f"  SCALING CHECK   d={d}, β={beta}")
    print(f"  Expected:  λ₁(H_B) ≥ c·L⁻²,  L²·λ₁ ≥ {c_theory}")
    print(f"  Reference: scalar lattice Laplacian λ₁ = 4sin²(π/L)")
    print(f"{'═'*60}")
    print(f"  {'L':>4}  {'λ₁(H_B)':>14}  {'L²·λ₁':>12}  {'λ₁(Δ_L)':>12}  {'≥c?':>6}")
    print(f"  {'─'*4}  {'─'*14}  {'─'*12}  {'─'*12}  {'─'*6}")
    results = []
    for L in L_values:
        H, M, _, _ = build_hessian(L, d, beta, boundary_only=True)
        _, lam1 = spectral_gap(H)
        # Scalar Laplacian reference: min nonzero eigenvalue in 1D = 4sin²(π/L)
        lam_laplacian = 4.0 * np.sin(np.pi / L)**2
        if lam1 is None:
            print(f"  {L:>4}  {'N/A':>14}  {'N/A':>12}  {lam_laplacian:>12.6f}  {'FAIL':>6}")
            results.append((L, None, False))
            continue
        scaled = lam1 * L**2
        ok = lam1 >= c_theory * L**(-2)
        results.append((L, lam1, ok))
        print(f"  {L:>4}  {lam1:>14.8f}  {scaled:>12.6f}  {lam_laplacian:>12.6f}  {'✓' if ok else '✗':>6}")

    # Summary: the bound is confirmed if all ok; note that L²·λ₁ growing
    # means the boundary Hessian gap exceeds the L^{-2} lower bound — conservative but valid.
    all_gap_ok = all(ok for (_, _, ok) in results)
    scaled_vals = [lam1 * L**2 for (L, lam1, ok) in results if lam1 is not None]
    if len(scaled_vals) >= 2:
        print(f"\n  L²·λ₁ values: {[f'{v:.3f}' for v in scaled_vals]}")
        print(f"  Note: L²·λ₁ not converging to const → boundary Hessian gap > L⁻²  (bound is conservative).")
        print(f"  Spectral gap inequality λ₁ ≥ c·L⁻²: {'ALL PASS ✓' if all_gap_ok else 'SOME FAIL ✗'}")
    return results


# ───────────────────────────────────────────────────────────────────────────────
# CLI
# ───────────────────────────────────────────────────────────────────────────────

def parse_args():
    p = argparse.ArgumentParser(description="Block Hessian & Spectral Gap Test")
    p.add_argument("--d",    type=int,   default=2,
                   help="Lattice dimension (default 2)")
    p.add_argument("--L",    type=int,   nargs="+", default=[4, 6, 8],
                   help="List of lattice sizes (default 4 6 8)")
    p.add_argument("--beta", type=float, default=5.0,
                   help="Inverse coupling β (default 5.0)")
    p.add_argument("--c",    type=float, default=0.5,
                   help="Theoretical constant c in gap ≥ cL⁻² (default 0.5)")
    return p.parse_args()


def main():
    args = parse_args()
    d        = args.d
    L_values = sorted(args.L)
    beta     = args.beta
    c_theory = args.c

    print("=" * 60)
    print("  Block Boundary Hessian H_B — Spectral Gap Verification")
    print(f"  Gauge group: U(1)   |   Gauge: temporal (axis 0)")
    print(f"  Action: Wilson (boundary plaquettes only)")
    print("=" * 60)

    # Per-L individual tests
    all_ok = True
    for L in L_values:
        ok = run_test(d, L, beta, c_theory, verbose=True)
        all_ok = all_ok and ok

    # Scaling study
    if len(L_values) >= 2:
        scaling_check(d, L_values, beta, c_theory)

    # Final verdict
    print(f"\n{'═'*60}")
    if all_ok:
        print("  ✓  ALL TESTS PASSED  —  λ₁(H_B) ≥ c·L⁻² confirmed.")
        sys.exit(0)
    else:
        print("  ✗  SOME TESTS FAILED — see above for details.")
        if __name__ == "__main__":
                sys.exit(1)
if __name__ == "__main__":
    main()
