def intervals_chain(k, L=1):
    return [(i, i + L) for i in range(k)]

def has_global_overlap(intervals):
    left = max(a for a, _ in intervals)
    right = min(b for _, b in intervals)
    return left <= right

def test_previous_chain_length_counterexample():
    intervals = intervals_chain(10, 1)
    assert not has_global_overlap(intervals)
