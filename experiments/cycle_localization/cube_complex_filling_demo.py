from collections import Counter

def plaquette_boundary(x, y):
    return [
        ((x, y), (x + 1, y)),
        ((x + 1, y), (x + 1, y + 1)),
        ((x + 1, y + 1), (x, y + 1)),
        ((x, y + 1), (x, y)),
    ]

def rectangle_filling(x0, y0, w, h):
    return [(x, y) for x in range(x0, x0 + w) for y in range(y0, y0 + h)]

phi = rectangle_filling(2, 3, 2, 1)

edge_count = Counter()
for px, py in phi:
    for e in plaquette_boundary(px, py):
        edge_count[e] += 1

boundary = [e for e, c in edge_count.items() if c % 2 == 1]

vertices = set()
for a, b in boundary:
    vertices.add(a)
    vertices.add(b)

xs = [v[0] for v in vertices]
ys = [v[1] for v in vertices]
diameter = (max(xs) - min(xs)) + (max(ys) - min(ys))

print("filling plaquettes:", len(phi))
print("boundary edges:", len(boundary))
print("support diameter:", diameter)
print("bounded radius witness:", diameter <= 6)
