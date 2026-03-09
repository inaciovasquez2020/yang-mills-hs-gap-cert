import numpy as np

def random_hamiltonian(n):
    A = np.random.randn(n,n)
    return A.T @ A

def test_domination():
    np.random.seed(3)

    n = 12
    H = random_hamiltonian(n)

    R = np.zeros((n,n))
    for i in range(n):
        for j in range(n):
            if i != j:
                d = np.random.rand()*10
                R[i,j] = -d
                R[i,i] += d

    eigH = np.linalg.eigvalsh(H)
    eigR = np.linalg.eigvalsh(R)

    gapR = eigR[1]

    C = eigH[0]/gapR if gapR>0 else 0

    print("min eigenvalue H:", eigH[0])
    print("R gap:", gapR)
    print("candidate domination constant:", C)

if __name__ == "__main__":
    test_domination()
