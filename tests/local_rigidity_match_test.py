import numpy as np

def laplacian(n):
    L=np.zeros((n,n))
    for i in range(n):
        L[i,i]=2
        L[i,(i-1)%n]=-1
        L[i,(i+1)%n]=-1
    return L

def local_rigidity(n):
    R=np.zeros((n,n))
    for i in range(n):
        R[i,i]+=2
        R[i,(i-1)%n]-=1
        R[i,(i+1)%n]-=1
    return R

def run():
    for n in [10,20,40,80]:
        H=laplacian(n)
        R=local_rigidity(n)

        eigH=np.linalg.eigvalsh(H)
        eigR=np.linalg.eigvalsh(R)

        C=eigH[1]/eigR[1]

        print("size:",n)
        print("C:",C)
        print()

if __name__=="__main__":
    run()
