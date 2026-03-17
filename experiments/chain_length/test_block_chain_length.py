import numpy as np

L = 1
R = 4

blocks = [i for i in range(10)]

def chain_length(blocks):
    return len(blocks)

k = chain_length(blocks)

print("chain_length",k)
print("R/L bound",R/L)
