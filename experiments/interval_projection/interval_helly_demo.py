def has_global_overlap(intervals):
    left = max(a for a,_ in intervals)
    right = min(b for _,b in intervals)
    return left <= right

intervals = [(0,3),(1,4),(2,5),(2,6)]
print("intervals:",intervals)
print("global_overlap:",has_global_overlap(intervals))
