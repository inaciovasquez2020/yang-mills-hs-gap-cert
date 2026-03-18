import json
import math

def test_scaling_invariant():
    with open("results/block_poincare/block_poincare_scaling.json") as f:
        data = json.load(f)["block_poincare_scaling"]

    values = []
    for entry in data:
        L = entry["L"]
        scaled = entry["scaled_mean"]
        values.append(scaled * (L ** 2))

    mean_val = sum(values) / len(values)
    for v in values:
        assert abs(v - mean_val) / mean_val < 0.2
