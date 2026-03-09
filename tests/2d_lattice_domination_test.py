import numpy as np

def grid_laplacian(n):
    N=n*n
    L=np.zeros((N,N))

    def idx(i,j):
        return i*n+j

    for i in range(n):
        for j in range(n):
            k=idx(i,j)

            for di,dj in [(-1,0),(1,0),(0,-1),(0,1)]:
                ni=(i+di)%n
                nj=(j+dj)%n
                L[k,k]+=1
                L[k,idx(ni,nj)]-=1

    return L

def run():
    for n in [4,6,8]:

        H=grid_laplacian(n)
        R=grid_laplacian(n)

        eigH=np.linalg.eigvalsh(H)
        eigR=np.linalg.eigvalsh(R)

        C=eigH[1]/eigR[1]

        print("grid:",n,"x",n)
        print("C:",C)
        print()

if __name__=="__main__":
    run()
