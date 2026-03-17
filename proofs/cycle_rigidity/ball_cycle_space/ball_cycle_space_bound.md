# Ball Cycle-Space Bound

Let G be a graph of maximum degree Δ.
Fix v and radius R.
Let H = B_R(v).

## Step 1. Vertex bound

Every vertex in H lies at graph distance at most R from v.
At distance j there are at most Δ^j vertices.
Therefore

|V(H)| <= 1 + Δ + Δ^2 + ... + Δ^R.

Hence

|V(H)| = O(Δ^R).

## Step 2. Edge bound

Since every vertex has degree at most Δ,

2|E(H)| <= Δ |V(H)|.

Thus

|E(H)| <= (Δ/2)|V(H)|.

Hence

|E(H)| = O(Δ^{R+1}).

## Step 3. Cycle-space rank

For any finite graph H,

dim Z1(H) = |E(H)| - |V(H)| + c(H)

where c(H) is the number of connected components.

If H is connected, then

dim Z1(H) = |E(H)| - |V(H)| + 1.

Therefore

dim Z1(B_R(v)) <= |E(B_R(v))| - |V(B_R(v))| + 1
<= (Δ/2)|V(B_R(v))| - |V(B_R(v))| + 1
= O(Δ^{R+1}).

## Conclusion

There exists f(Δ,R) such that

dim Z1(B_R(v)) <= f(Δ,R)

and one may take

f(Δ,R) = O(Δ^{R+1}).
