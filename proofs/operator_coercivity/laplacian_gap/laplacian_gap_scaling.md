# Laplacian Gap Scaling

For the n x n grid graph G_n,

lambda_1(G_n) = second-smallest eigenvalue of the graph Laplacian.

Empirical data:

n = 6   -> lambda_1 = 0.2679491924311212
n = 8   -> lambda_1 = 0.1522409349774257
n = 10  -> lambda_1 = 0.09788696740969027
n = 12  -> lambda_1 = 0.06814834742186186
n = 14  -> lambda_1 = 0.050144175636351235

Heuristic scaling:

lambda_1(G_n) ~ c n^(-2)

Therefore

lambda_1(G_n)^(-1) = O(n^2),

which matches the coercivity scale

||g||^2 <= C n^2 <g,(-Delta_G)g>.
