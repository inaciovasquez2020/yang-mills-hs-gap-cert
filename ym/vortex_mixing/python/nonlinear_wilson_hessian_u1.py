import numpy as np

def idx(x, y, L):
    return (x % L) + L * (y % L)

def e_x(x, y, L):
    return idx(x, y, L)

def e_y(x, y, L):
    return L*L + idx(x, y, L)

def build_C(L):
    nE = 2 * L * L
    nF = L * L
    C = np.zeros((nF, nE))
    for y in range(L):
        for x in range(L):
            f = idx(x, y, L)
            C[f, e_x(x, y, L)] = 1
            C[f, e_y(x+1, y, L)] = 1
            C[f, e_x(x, y+1, L)] = -1
            C[f, e_y(x, y, L)] = -1
    return C

def wilson_u1_energy(theta, L, beta=1.0):
    C = build_C(L)
    phi = C @ theta
    return float(beta * np.sum(1.0 - np.cos(phi)))

def finite_diff_hessian(f, x0, eps=1e-6):
    n = x0.size
    H = np.zeros((n, n))
    fx = f(x0)
    for i in range(n):
        ei = np.zeros(n); ei[i] = 1.0
        fip = f(x0 + eps*ei)
        fim = f(x0 - eps*ei)
        H[i, i] = (fip - 2.0*fx + fim) / (eps*eps)
        for j in range(i+1, n):
            ej = np.zeros(n); ej[j] = 1.0
            fpp = f(x0 + eps*ei + eps*ej)
            fpm = f(x0 + eps*ei - eps*ej)
            fmp = f(x0 - eps*ei + eps*ej)
            fmm = f(x0 - eps*ei - eps*ej)
            Hij = (fpp - fpm - fmp + fmm) / (4.0*eps*eps)
            H[i, j] = Hij
            H[j, i] = Hij
    return H

def analytic_hessian_at_vacuum(L, beta=1.0):
    C = build_C(L)
    return beta * (C.T @ C)

def coexact_projector(L, tol=1e-10):
    C = build_C(L)
    U, s, Vt = np.linalg.svd(C.T, full_matrices=False)
    r = int(np.sum(s > tol))
    if r == 0:
        return np.zeros((2*L*L, 2*L*L))
    Q = U[:, :r]
    return Q @ Q.T

def min_pos_eig(A, tol=1e-8):
    e = np.linalg.eigvalsh(0.5*(A + A.T))
    pos = e[e > tol]
    return None if pos.size == 0 else float(np.min(pos))

def estimate_coexact_poincare_constant(Ls, beta=1.0):
    vals = []
    for L in Ls:
        H = analytic_hessian_at_vacuum(L, beta=beta)
        P = coexact_projector(L)
        Hc = P @ H @ P
        lam = min_pos_eig(Hc)
        if lam is None:
            continue
        vals.append(lam * (L**2))
    if len(vals) == 0:
        return None
    return float(np.min(vals)), float(np.max(vals)), np.array(vals, dtype=float)

def main():
    L = 4
    beta = 1.0
    nE = 2*L*L
    x0 = np.zeros(nE)
    f = lambda th: wilson_u1_energy(th, L=L, beta=beta)
    H_fd = finite_diff_hessian(f, x0, eps=1e-6)
    H_an = analytic_hessian_at_vacuum(L, beta=beta)
    diff = np.max(np.abs(H_fd - H_an))
    print(f"U(1) Wilson Hessian check at vacuum: L={L}, beta={beta}, max|H_fd-H_an|={diff:.3e}")
    Ls = [4, 6, 8, 10, 12]
    lo, hi, arr = estimate_coexact_poincare_constant(Ls, beta=beta)
    print(f"Coexact scaled constants beta*lambda_min(L)*L^2 over {Ls}: min={lo:.6f}, max={hi:.6f}")
    print(arr)

if __name__ == "__main__":
    main()
