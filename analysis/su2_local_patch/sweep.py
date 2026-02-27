import numpy as np
from su2_patch_numeric import estimate_constants

for n in [80,120,160,200,250]:
    gap, eigL, eigV = estimate_constants(n)
    print(n, gap)
