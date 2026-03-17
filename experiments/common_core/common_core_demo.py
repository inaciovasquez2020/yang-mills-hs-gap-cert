import numpy as np

def local_operator(L, m=6):
    diag = np.array([1.0 + (j + 1) / L for j in range(m)])
    return np.diag(diag)

def q_L(L, f):
    A = local_operator(L, len(f))
    return float(f @ A @ f)

def q_inf(f):
    A = np.diag(np.ones(len(f)))
    return float(f @ A @ f)

def finitely_supported_vectors(m=6):
    return [
        np.array([1.0, 0.0, 0.0, 0.0, 0.0, 0.0])[:m],
        np.array([1.0, -1.0, 0.5, 0.0, 0.0, 0.0])[:m],
        np.array([0.0, 0.0, 1.0, -2.0, 1.0, 0.0])[:m],
    ]

def run():
    fs = finitely_supported_vectors()
    for idx, f in enumerate(fs):
        print("vector", idx, "q_inf", q_inf(f))
        vals = []
        for L in [8, 12, 20, 40, 80, 160]:
            val = q_L(L, f)
            vals.append(val)
            print("L", L, "q_L", val, "error", abs(val - q_inf(f)))
        print("uniform_upper_bound", max(vals))
        print("")

if __name__ == "__main__":
    run()
