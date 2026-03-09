import numpy as np

def random_curvature(n):
    return np.random.randn(n)

def curvature_distance(F1, F2):
    return np.sum((F1 - F2) ** 2)

def build_rigidity_matrix(curvatures):
    m = len(curvatures)
    R = np.zeros((m, m))
    for i in range(m):
        for j in range(m):
            if i != j:
                d = curvature_distance(curvatures[i], curvatures[j])
                R[i, j] = -d
                R[i, i] += d
    return R

def run_test():
    np.random.seed(2)
    m = 12
    n = 40

    curvatures = [random_curvature(n) for _ in range(m)]
    R = build_rigidity_matrix(curvatures)

    eigvals = np.linalg.eigvalsh(R)

    print("Rigidity matrix eigenvalues:")
    print(eigvals)

    smallest = eigvals[0]
    second = eigvals[1]

    print("Smallest eigenvalue:", smallest)
    print("Second eigenvalue:", second)

    if smallest < 1e-8 and second > 0:
        print("PASS: vacuum kernel detected with positive spectral gap")
    else:
        print("WARNING: spectral structure not as expected")

if __name__ == "__main__":
    run_test()
