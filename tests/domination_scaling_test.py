import numpy as np

def random_hamiltonian(n):
    A = np.random.randn(n,n)
    return A.T @ A

def build_rigidity(n):
    R = np.zeros((n,n))
    for i in range(n):
        for j in range(n):
            if i!=j:
                d=np.random.rand()*10
                R[i,j]=-d
                R[i,i]+=d
    return R

def run():
    np.random.seed(5)

    for n in [10,20,40,80]:
        H=random_hamiltonian(n)
        R=build_rigidity(n)

        eigH=np.linalg.eigvalsh(H)
        eigR=np.linalg.eigvalsh(R)

        gapR=eigR[1]
        C=eigH[0]/gapR if gapR>0 else 0

        print("size:",n)
        print("C:",C)
        print()

if __name__=="__main__":
    run()
