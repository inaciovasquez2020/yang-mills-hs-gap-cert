import numpy as np

def conditional_mutual_information(cov_PP, cov_FF, cov_BB, cov_PF, cov_PB, cov_FB):
    def logdet(M):
        return np.log(np.linalg.det(M))
    return 0.5 * (
        logdet(cov_PP) + logdet(cov_FF) + logdet(cov_BB)
        - logdet(np.block([[cov_PP, cov_PB],[cov_PB.T, cov_BB]]))
        - logdet(np.block([[cov_FF, cov_FB],[cov_FB.T, cov_BB]]))
        + logdet(np.block([[cov_PP, cov_PB, cov_PF],
                            [cov_PB.T, cov_BB, cov_FB.T],
                            [cov_PF.T, cov_FB, cov_FF]]))
    )

def toy_gauge_orbit_entropy(area, strength=1.0):
    return strength * area

areas = [4, 8, 16, 32]
for A in areas:
    entropy = toy_gauge_orbit_entropy(A)
    print(f"Area={A}, lower-bound entropy={entropy}")
