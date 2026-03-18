import numpy as np
from math import exp, pi

def theta(x, N=200):
    s = 0.0
    for n in range(-N, N+1):
        s += exp(-pi * n * n * x)
    return s

def E(z, U=6.0, M=2001):
    u = np.linspace(-U, U, M)
    du = u[1] - u[0]
    x = np.exp(u)
    integrand = np.array([theta(xi) * (xi**(1j*z)) for xi in x])
    return np.trapezoid(integrand, dx=du)

def test_HB():
    xs = np.linspace(-5, 5, 21)
    ys = [0.5, 1.0, 2.0]
    for y in ys:
        print("y =", y)
        for x in xs:
            z = x + 1j*y
            val = abs(E(z))**2 - abs(E(np.conjugate(z)))**2
            print(f"x={x:.2f}, diff={val.real:.6e}")
        print()

if __name__ == "__main__":
    test_HB()
