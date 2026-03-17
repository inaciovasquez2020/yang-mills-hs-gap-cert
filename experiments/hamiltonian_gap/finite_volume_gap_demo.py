import numpy as np

def finite_volume_gap(L, kappa=1.0, c=1.0):
    return kappa * c / (L**2)

def run():
    print("L,m_L")
    for L in [4, 6, 8, 10, 12, 16, 20]:
        print(f"{L},{finite_volume_gap(L):.8f}")

if __name__ == "__main__":
    run()
