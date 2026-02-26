import argparse, numpy as np

def lambda1_1d_dirichlet(n: int, h: float) -> float:
    # 1D Dirichlet Laplacian on interior points 1..n with spacing h:
    # eigenvalues: (2-2cos(kπ/(n+1)))/h^2
    k = 1
    return (2.0 - 2.0*np.cos(k*np.pi/(n+1))) / (h*h)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--R", type=float, required=True)
    ap.add_argument("--n", type=int, default=200, help="# interior points per axis for cube [-R,R]")
    args = ap.parse_args()

    R = args.R
    n = args.n
    # spacing for cube [-R,R] with n interior points and Dirichlet boundary at ±R:
    h = (2.0*R)/(n+1)

    lam1_1d = lambda1_1d_dirichlet(n, h)
    # 3D cube Dirichlet: λ1 = λ1x+λ1y+λ1z with k=1 in each
    lam1_3d = 3.0*lam1_1d

    print(f"R={R} n={n} h={h}")
    print(f"lambda1_approx (cube Dirichlet) ~ {lam1_3d}")
    print(f"R^2 * lambda1 ~ {R*R*lam1_3d}  (should approach constant)")
