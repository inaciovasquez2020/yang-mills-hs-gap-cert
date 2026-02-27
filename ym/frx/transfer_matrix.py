import numpy as np

def row_stochasticize(W):
    """
    Convert a matrix to row-stochastic form by normalizing rows
    """
    row_sums = W.sum(axis=1)
    # Avoid division by zero
    row_sums = np.where(row_sums == 0, 1.0, row_sums)
    return W / row_sums[:, np.newaxis]

def lazy_uniform_kernel(m, alpha):
    """
    Lazy uniform kernel on m states:
    P = alpha*I + (1-alpha)*uniform
    """
    P = np.zeros((m, m))
    for i in range(m):
        P[i, i] = alpha
        for j in range(m):
            if j != i:
                P[i, j] = (1.0 - alpha) / (m - 1)
    return P

def dobrushin_tv_contraction(P):
    """
    Compute Dobrushin contraction coefficient:
    ρ = max_i,j (1/2) ∑_k |P[i,k] - P[j,k]|
    """
    m = P.shape[0]
    max_dist = 0.0
    for i in range(m):
        for j in range(i+1, m):
            dist = 0.5 * np.sum(np.abs(P[i, :] - P[j, :]))
            max_dist = max(max_dist, dist)
    return max_dist

def transfer_matrix_contraction_rate(W):
    """
    For a transfer matrix W, compute contraction rate
    """
    P = row_stochasticize(W)
    return dobrushin_tv_contraction(P)

def toy_confining_kernel(m, g=0.5):
    """
    Toy confining kernel that favors staying near diagonal
    """
    W = np.zeros((m, m))
    for i in range(m):
        for j in range(m):
            W[i, j] = np.exp(-g * abs(i - j))
    return W

def weyl_sequence_obstruction(W, tol=1e-10):
    """
    Check for Weyl sequence obstruction (spectral gap vanishing)
    """
    P = row_stochasticize(W)
    # Compute second eigenvalue
    evals = np.linalg.eigvals(P)
    # Sort in descending order by real part
    evals_sorted = sorted(evals, key=lambda x: -np.real(x))
    if len(evals_sorted) > 1:
        gap = 1.0 - abs(evals_sorted[1])
        return gap < tol
    return False
