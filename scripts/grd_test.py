import argparse
import numpy as np
def paulis():
I = np.array([[1,0],[0,1]], dtype=complex)
X = np.array([[0,1],[1,0]], dtype=complex)
Y = np.array([[0,-1j],[1j,0]], dtype=complex)
Z = np.array([[1,0],[0,-1]], dtype=complex)
return [I,X,Y,Z]
P = paulis()
def kron_all(mats):
out = mats[0]
for m in mats[1:]:
out = np.kron(out, m)
return out
def embed_single(N, i, M):
mats = [P[0]] * N
mats[i] = M
return kron_all(mats)
def embed_two(N, i, j, Mi, Mj):
mats = [P[0]] * N
mats[i] = Mi
mats[j] = Mj
return kron_all(mats)
def op_norm(A):
return np.linalg.norm(A, 2)
def comm(A, B):
return A @ B - B @ A
def pauli_strings(N):
total = 4**N
digs = np.zeros((total, N), dtype=int)
for idx in range(total):
x = idx
for k in range(N):
digs[idx, N-1-k] = x % 4
x //= 4
return digs
def string_support(row):
return set(np.nonzero(row != 0)[0].tolist())
def neighborhood_interval(S, r, N):
if not S:
return set()
lo = max(0, min(S) - r)
hi = min(N-1, max(S) + r)
return set(range(lo, hi+1))
def pauli_basis_operators(N):
digs = pauli_strings(N)
ops = []
for row in digs:
mats = [P[int(t)] for t in row]
ops.append(kron_all(mats))
return digs, ops
def decompose_in_pauli(A, digs, ops):
N = digs.shape[1]
dim = 2**N
coeffs = np.zeros(len(ops), dtype=complex)
for k, Ok in enumerate(ops):
coeffs[k] = np.trace(Ok.conj().T @ A) / dim
return coeffs
def weight_outside_neighborhood(coeffs, digs, S, r, N):
nb = neighborhood_interval(S, r, N)
w = 0.0
for k, row in enumerate(digs):
supp = string_support(row)
if supp and not supp.issubset(nb):
w += abs(coeffs[k])**2
return float(np.sqrt(w))
def build_local_H(N, seed, delocalized=False, R=0, eps=0.0):
rng = np.random.default_rng(seed)
H = np.zeros((2N, 2N), dtype=complex)
for i in range(N-1):
a = rng.integers(1,4)
b = rng.integers(1,4)
J = rng.normal()
H += J * embed_two(N, i, i+1, P[a], P[b])
for i in range(N):
a = rng.integers(1,4)
h = rng.normal()
H += h * embed_single(N, i, P[a])
if delocalized:
a = rng.integers(1,4)
b = rng.integers(1,4)
H += eps * embed_two(N, 0, min(N-1, R), P[a], P[b])
return 0.5 * (H + H.conj().T)
def build_local_A(N, center):
A = embed_single(N, center, P[1])
return 0.5 * (A + A.conj().T)
def main():
ap = argparse.ArgumentParser()
ap.add_argument("--N", type=int, default=8)
ap.add_argument("--nmax", type=int, default=8)
ap.add_argument("--r", type=int, default=2)
ap.add_argument("--seed", type=int, default=0)
ap.add_argument("--center", type=int, default=3)
ap.add_argument("--mode", choices=["grd","violate"], default="grd")
ap.add_argument("--R", type=int, default=7)
ap.add_argument("--eps", type=float, default=1.0)
ap.add_argument("--alpha", type=float, default=12.0)
ap.add_argument("--beta", type=float, default=0.7)
args = ap.parse_args()
N = args.N
if args.mode == "grd":
    H = build_local_H(N, args.seed)
else:
    H = build_local_H(N, args.seed, True, args.R, args.eps)

A0 = build_local_A(N, args.center)
S0 = {args.center}

digs, ops = pauli_basis_operators(N)
X = A0.copy()
base = op_norm(A0) + 1e-12

passed = True
for n in range(1, args.nmax + 1):
    X = comm(H, X)
    cn = op_norm(X) / base
    coeffs = decompose_in_pauli(X, digs, ops)
    leak = weight_outside_neighborhood(coeffs, digs, S0, args.r, N) / (np.linalg.norm(coeffs) + 1e-12)
    rhs = np.math.factorial(n) * (args.alpha ** n) * np.exp(-args.beta * args.r)
    print(f"n={n} ad_norm={cn:.3e} rhs={rhs:.3e} leak={leak:.3e}")
    if args.mode == "grd":
        if cn > 5.0 * rhs or leak > 0.25:
            passed = False
    else:
        if leak < 0.25:
            passed = False

raise SystemExit(0 if passed else 1)
if name == "main":
main()
