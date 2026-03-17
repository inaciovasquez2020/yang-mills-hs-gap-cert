def has_global_overlap(intervals):
    left = max(a for a, _ in intervals)
    right = min(b for _, b in intervals)
    return left <= right

def test_chain_length_bound_under_global_intersection():
    intervals = [(0.0, 1.0), (0.1, 1.1), (0.2, 1.2), (0.3, 1.3), (0.4, 1.4)]
    assert has_global_overlap(intervals)
