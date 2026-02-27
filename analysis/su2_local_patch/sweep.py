from su2_patch_numeric import estimate_constants

for n in [80,120,160,200,250,320,400]:
    gapH, gapL, minV = estimate_constants(n=n, k=12, seed=0)
    print(n, gapH, gapL, minV)
