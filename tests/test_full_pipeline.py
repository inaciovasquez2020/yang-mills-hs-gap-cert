import numpy as np
from src.block.block_partition import partition_indices, block_variance
from src.operators.gradient import gradient_energy

def test():
    n = 400
    L = 20

    g = np.random.randn(n)
    g = g - np.mean(g)

    blocks = partition_indices(n, L)

    lhs = block_variance(g, blocks)
    rhs = L**2 * gradient_energy(g)

    print("lhs:", lhs)
    print("rhs:", rhs)
    print("inequality:", lhs <= rhs)

test()
