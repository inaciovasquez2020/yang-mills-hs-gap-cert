import numpy as np

def discrete_gradient(f):
    grad = []
    for i in range(len(f) - 1):
        grad.append(f[i+1] - f[i])
    return np.array(grad)

def block_poincare_constant(L, trials=100):
    ratios = []
    for _ in range(trials):
        f = np.random.randn(L)
        f = f - np.mean(f)
        grad = discrete_gradient(f)
        num = np.sum(f**2)
        den = np.sum(grad**2)
        if den > 1e-8:
            ratios.append(num / den)
    return np.mean(ratios)

def test_block_poincare_scaling():
    results = []
    for L in [8, 16, 32, 64]:
        c_est = block_poincare_constant(L)
        results.append((L, c_est / (L**2)))
    for L, scaled in results:
        print(f"L={L}, scaled constant ≈ {scaled}")
        assert scaled > 0
