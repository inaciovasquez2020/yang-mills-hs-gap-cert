import numpy as np
import matplotlib.pyplot as plt

volumes = np.array([100, 200, 300, 400, 500, 600])
gaps = np.array([0.2024, 0.06474, 0.03076, 0.01808, 0.00753, 0.00443])

# Create log-log plot
plt.figure(figsize=(10, 6))
plt.loglog(volumes, gaps, 'bo-', linewidth=2, markersize=8, label='Numerical data')

# Fit line
log_v = np.log(volumes)
log_g = np.log(gaps)
p, log_c = np.polyfit(log_v, log_g, 1)
c = np.exp(log_c)
fit_line = c * volumes**p
plt.loglog(volumes, fit_line, 'r--', linewidth=2, 
           label=f'Fit: ∝ volume$^{{{p:.3f}}}$')

# Reference lines
plt.loglog(volumes, 20/volumes, 'g:', linewidth=2, label='1/volume')
plt.loglog(volumes, 2000/volumes**2, 'm:', linewidth=2, label='1/volume²')

plt.xlabel('Volume (patches × n)', fontsize=12)
plt.ylabel('Spectral Gap', fontsize=12)
plt.title('Gap Scaling with Volume', fontsize=14)
plt.legend(fontsize=10)
plt.grid(True, alpha=0.3)
plt.tight_layout()
plt.savefig('gap_scaling.png', dpi=150)
print("Saved gap_scaling.png")

print("\n" + "="*50)
print("SCALING ANALYSIS")
print("="*50)
print(f"Gap = {c:.2f} × volume^{p:.3f}")
print(f"Expected exponents:")
print(f"  - Pure Laplacian: p = -2.0 (1/volume²)")
print(f"  - With mass term: p = -1.0 (1/volume) → constant in physical units")
print(f"\nYour result p = {p:.3f} is closer to -2.0, indicating:")
print("The numerical experiment is measuring the Laplacian scaling")
print("This confirms the need for the Wilson action's constant term")
print("to provide the mass gap that changes p from -2.0 to -1.0")
