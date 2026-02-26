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

def build_local_H(N, seed):
    rng = np.random.default_rng(seed)
    dim = 2**N
    H = np.zeros((dim, dim), dtype=complex)
    for i in range(N-1):
        H += embed_two(N, i, i+1, P[1], P[2])
    return 0.5 * (H + H.conj().T)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=6)
    ap.add_argument("--mode", choices=["grd","violate"], default="grd")
    args = ap.parse_args()

    H = build_local_H(args.N, 0)
    A = embed_single(args.N, args.N//2, P[1])

    X = comm(H, A)
    print("ok", np.linalg.norm(X))

if __name__ == "__main__":
    main()
