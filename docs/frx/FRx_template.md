FRx (Transfer-Matrix Contraction) Template

Data:
- Finite state space size m
- Row-stochastic kernel P on {1,...,m}
- Total variation norm ||p-q||_TV = (1/2) sum_j |p_j-q_j|

FRx inequality (TV contraction):
There exists rho in [0,1) such that for all probability vectors p,q and all t >= 0,
|| p P^t - q P^t ||_TV <= rho^t || p - q ||_TV

Sufficient check (Doeblin):
If there exists alpha in (0,1) and a probability vector nu with
P(i,·) = (1-alpha) Q(i,·) + alpha nu(·) for all i
then rho <= 1-alpha.

Toy confining kernel (lazy-uniform):
P = (1-alpha) I + alpha U, where U has all entries 1/m.
Then rho = 1-alpha exactly, spectral gap = alpha.
