def has_global_overlap(intervals):
    left = max(a for a,_ in intervals)
    right = min(b for _,b in intervals)
    return left <= right

def test_interval_helly():
    intervals = [(0,3),(1,4),(2,5)]
    assert has_global_overlap(intervals)
