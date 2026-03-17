from collections import Counter

def square_cycle(x, y):
    return [
        ((x, y), (x + 1, y)),
        ((x + 1, y), (x + 1, y + 1)),
        ((x + 1, y + 1), (x, y + 1)),
        ((x, y + 1), (x, y)),
    ]

def plaquette_boundary(x, y):
    return square_cycle(x, y)

gamma = square_cycle(3, 4)
phi = [(3, 4)]

edge_count = Counter()
for px, py in phi:
    for e in plaquette_boundary(px, py):
        edge_count[e] += 1

boundary = [e for e, c in edge_count.items() if c % 2 == 1]

print("cycle edges:", len(gamma))
print("filling plaquettes:", len(phi))
print("boundary edges:", len(boundary))
print("boundary matches cycle:", len(boundary) == len(gamma))
