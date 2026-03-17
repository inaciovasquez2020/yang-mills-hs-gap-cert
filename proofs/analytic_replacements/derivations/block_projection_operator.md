# Block Projection Operator

Let \(P_L\) be the block averaging operator on blocks of side length \(L\).

For a function \(f\),

\[
(P_L f)(x) = \frac{1}{|B_L|} \sum_{y\in B_L(x)} f(y).
\]

Define the fluctuation operator

\[
Q_L = I - P_L.
\]

Then

\[
\|Q_L f\|^2 = \sum_x (f(x)-P_L f(x))^2.
\]
