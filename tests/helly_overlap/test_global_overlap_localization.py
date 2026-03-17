def has_global_overlap(intervals):
    left = max(a for a, _ in intervals)
    right = min(b for _, b in intervals)
    return left <= right

def chain_diameter(intervals):
    left = min(a for a, _ in intervals)
    right = max(b for _, b in intervals)
    return right - left

def test_global_overlap_localization():
    intervals = [(0.0, 1.0), (0.2, 1.2), (0.4, 1.4), (0.6, 1.6)]
    assert has_global_overlap(intervals)
    assert chain_diameter(intervals) <= 2
