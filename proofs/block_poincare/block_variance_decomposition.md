# Block Variance Decomposition

Statement:

||g||^2 = sum_B ||g - g_B||_{L^2(B)}^2

Assumption:
P_L g = 0

Definitions:

g_B = (1/|B|) ∫_B g(x) dx

Result:

For each block B,

||g||_{L^2(B)}^2 =
||g - g_B||_{L^2(B)}^2 + |B| g_B^2

Since P_L g = 0, g_B = 0.

Thus

||g||^2 = sum_B ||g - g_B||_{L^2(B)}^2
