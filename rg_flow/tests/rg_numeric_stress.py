#!/usr/bin/env python3
import math

beta0 = 1.0
logb = 0.5

def step(g):
    return math.sqrt(g*g / (1 + 2*beta0*g*g*logb))

g = 0.5
for n in range(20):
    print(n, g)
    g = step(g)
