import numpy as np
from src.block.block_partition import partition_indices, block_variance
from src.operators.gradient import gradient_energy

def run():
    n = 800
    L = 20

    g = np.random.randn(n)
    g = g - np.mean(g)

    blocks = partition_indices(n, L)

    block_var = block_variance(g, blocks)
    grad = gradient_energy(g)

    print("block variance:", block_var)
    print("CL^2 grad:", L**2 * grad)
    print("bound holds:", block_var <= L**2 * grad)

if __name__ == "__main__":
    run()
