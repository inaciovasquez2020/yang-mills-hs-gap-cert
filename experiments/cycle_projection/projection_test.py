import numpy as np

def orthogonal_projection(vectors, f):
    V = np.column_stack(vectors)
    proj = V @ np.linalg.pinv(V) @ f
    return proj

def run():
    dim = 50
    num_cycles = 5

    cycle_vectors = [np.random.randn(dim) for _ in range(num_cycles)]
    f = np.random.randn(dim)

    proj = orthogonal_projection(cycle_vectors,f)
    residual = f - proj

    print("||f||:", np.linalg.norm(f))
    print("||projection||:", np.linalg.norm(proj))
    print("||residual||:", np.linalg.norm(residual))

run()
