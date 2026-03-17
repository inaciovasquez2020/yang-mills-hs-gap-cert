def intervals_chain(k, L=1):
    return [(i, i + L) for i in range(k)]

def has_global_overlap(intervals):
    left = max(a for a, _ in intervals)
    right = min(b for _, b in intervals)
    return left <= right

def chain_diameter(intervals):
    left = min(a for a, _ in intervals)
    right = max(b for _, b in intervals)
    return right - left

def run():
    print("counterexample_family")
    ints = intervals_chain(10, 1)
    print("intervals:", ints)
    print("global_overlap:", has_global_overlap(ints))
    print("diameter:", chain_diameter(ints))

    print("")
    print("global_overlap_family")
    ints2 = [(0, 1), (0.2, 1.2), (0.4, 1.4), (0.6, 1.6)]
    print("intervals:", ints2)
    print("global_overlap:", has_global_overlap(ints2))
    print("diameter:", chain_diameter(ints2))

if __name__ == "__main__":
    run()
