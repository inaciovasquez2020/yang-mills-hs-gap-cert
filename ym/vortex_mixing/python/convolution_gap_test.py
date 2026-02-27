import math
import random
from typing import Callable, List
from ym.vortex_mixing.python.su2 import SU2, haar_su2, mul, trace, random_axis, rotate_by_angle

def step_sampler_factory(kind: str, rng: random.Random) -> Callable[[], SU2]:
    if kind == "haar":
        return lambda: haar_su2(rng)
    if kind == "fixed_angle":
        theta = 1.1
        def sample():
            axis = random_axis(rng)
            return rotate_by_angle(axis, theta)
        return sample
    if kind == "two_point":
        g1 = rotate_by_angle((1.0,0.0,0.0), 1.0)
        g2 = rotate_by_angle((0.0,1.0,0.0), 1.3)
        return lambda: g1 if rng.random() < 0.5 else g2
    raise ValueError(kind)

def sample_product_distribution(step: Callable[[], SU2], M: int, n: int, rng: random.Random) -> List[float]:
    out = []
    for _ in range(n):
        g = step()
        for __ in range(M-1):
            g = mul(step(), g)
        out.append(trace(g))
    return out

def prob_trace_negative(samples: List[float]) -> float:
    return sum(1 for t in samples if t < 0.0) / max(1, len(samples))

def tv_lower_bound_from_event(p: float, q: float) -> float:
    return abs(p - q)

def estimate_prob_convergence(kind: str, Ms: List[int], n: int, seed: int = 0):
    rng = random.Random(seed)
    step = step_sampler_factory(kind, rng)
    results = []
    for M in Ms:
        tr = sample_product_distribution(step, M, n, rng)
        pneg = prob_trace_negative(tr)
        results.append((M, pneg))
    return results

def estimate_influence_surrogate(kind: str, M: int, n: int, seed: int = 0):
    rng = random.Random(seed)
    step = step_sampler_factory(kind, rng)

    tr1 = sample_product_distribution(step, M, n, rng)
    p1 = prob_trace_negative(tr1)

    if kind == "fixed_angle":
        theta2 = 1.1 + 0.35
        def step2():
            axis = random_axis(rng)
            return rotate_by_angle(axis, theta2)
    else:
        step2 = step

    tr2 = sample_product_distribution(step2, M, n, rng)
    p2 = prob_trace_negative(tr2)

    return p1, p2, tv_lower_bound_from_event(p1, p2)

def main():
    Ms = [1,2,4,8,16,32,64]
    n = 20000

    for kind in ["two_point", "fixed_angle", "haar"]:
        conv = estimate_prob_convergence(kind, Ms, n, seed=7)
        print("kind", kind)
        for M,p in conv:
            print(M, p, "dev_from_half", abs(p-0.5))
        print()

    kind = "fixed_angle"
    print("influence_surrogate", kind)
    for M in Ms:
        p1,p2,lb = estimate_influence_surrogate(kind, M, n, seed=11)
        print(M, p1, p2, "tv_lb", lb)

if __name__ == "__main__":
    main()
