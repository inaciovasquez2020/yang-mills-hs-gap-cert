import numpy as np

def random_curvature_field(n):
    return np.random.randn(n)

def curvature_distance(F1, F2):
    return np.sum((F1 - F2) ** 2)

def rigidity_quadratic_form(states, curvatures):
    m = len(states)
    value = 0.0
    for i in range(m):
        for j in range(m):
            d = curvature_distance(curvatures[i], curvatures[j])
            value += d * (states[i] - states[j]) ** 2
    return 0.5 * value

def run_test():
    np.random.seed(1)
    m = 10
    n = 50
    states = np.random.randn(m)
    curvatures = [random_curvature_field(n) for _ in range(m)]
    q = rigidity_quadratic_form(states, curvatures)
    print("Rigidity quadratic form value:", q)
    if q >= 0:
        print("PASS: rigidity operator quadratic form is non-negative")
    else:
        print("FAIL: quadratic form negative")

if __name__ == "__main__":
    run_test()
