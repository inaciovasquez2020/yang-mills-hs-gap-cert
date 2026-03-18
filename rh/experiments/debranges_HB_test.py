import numpy as np
from math import exp, pi

def theta(x, N=400):
    s = 0.0
    for n in range(-N, N + 1):
        s += exp(-pi * n * n * x)
    return s

def E(z, U=8.0, M=4001):
    u = np.linspace(-U, U, M)
    du = u[1] - u[0]
    x = np.exp(u)
    integrand = np.array([theta(xi) * (xi ** (1j * z)) for xi in x], dtype=np.complex128)
    return np.trapezoid(integrand, dx=du)

def test_HB():
    xs = np.linspace(-10, 10, 41)
    ys = [0.25, 0.5, 1.0, 2.0, 4.0]
    global_min = None
    global_arg = None
    for y in ys:
        print("y =", y)
        for x in xs:
            z = x + 1j * y
            diff = abs(E(z)) ** 2 - abs(E(np.conjugate(z))) ** 2
            print(f"x={x:.2f}, diff={diff.real:.12e}")
            if global_min is None or diff.real < global_min:
                global_min = diff.real
                global_arg = (x, y)
        print()
    print("global_min_diff", global_min)
    print("global_min_arg", global_arg)

if __name__ == "__main__":
    test_HB()
