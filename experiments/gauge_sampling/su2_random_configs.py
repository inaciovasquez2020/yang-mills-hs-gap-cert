import numpy as np

def random_su2():
    a = np.random.randn(4)
    a = a/np.linalg.norm(a)
    return a

configs = [random_su2() for _ in range(10)]

for i,c in enumerate(configs):
    print("config",i,c)
