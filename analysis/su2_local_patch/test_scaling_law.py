import numpy as np
import matplotlib.pyplot as plt

# Data from your runs
volumes = np.array([100, 200, 300, 400, 500, 600])  # patches * n
gaps = np.array([0.2024, 0.06474, 0.03076, 0.01808, 0.00753, 0.00443])

# Fit to power law gap = c * volume^p
log_v = np.log(volumes)
log_g = np.log(gaps)
p, log_c = np.polyfit(log_v, log_g, 1)
c = np.exp(log_c)

print(f"Gap scales as {c:.4f} × volume^{p:.3f}")
print(f"Expected p = -1.0 for 1/volume scaling")
print(f"Deviation: {p + 1:.4f}")
