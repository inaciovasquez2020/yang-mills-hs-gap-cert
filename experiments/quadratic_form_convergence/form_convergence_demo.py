import numpy as np

def q(L, f):
    A = np.diag([1.0 + 1.0/L, 2.0 + 1.0/L, 3.0 + 1.0/L])
    return float(f @ A @ f)

def q_inf(f):
    A = np.diag([1.0, 2.0, 3.0])
    return float(f @ A @ f)

def run():
    f = np.array([1.0, -2.0, 0.5])
    qstar = q_inf(f)
    print("q_inf", qstar)
    for L in [4, 6, 8, 10, 12, 16, 20, 40, 80]:
        print("L", L, "q_L", q(L, f), "error", abs(q(L, f) - qstar))

if __name__ == "__main__":
    run()
