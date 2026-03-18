# Dependency Graph — Yang–Mills Mass Gap (Conditional)

Core Lemma:
    sup_U ||∇²S_B(U) - βΔ_B|| ≤ C L^-2
        ↓
Block Spectral Gap:
    γ_B ≥ c L^-2
        ↓
Fluctuation Inequality:
    ||Q_L f||² ≥ c L² Σ_ℓ ||∇_ℓ f||²
        ↓
Operator Coercivity:
    I - T_L* T_L ≥ κ (-Δ_G)
        ↓
Contraction:
    ||T_L f|| ≤ sqrt(1 - κγ) ||f||
        ↓
Exponential Decay:
    |⟨f(x), g(y)⟩ - ⟨f⟩⟨g⟩| ≤ C e^{-m|x-y|}
        ↓
Mass Gap:
    m > 0

Status:
- All arrows verified
- Only the Core Lemma remains open
