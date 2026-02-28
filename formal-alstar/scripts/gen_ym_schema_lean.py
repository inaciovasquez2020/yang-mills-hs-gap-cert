import csv, sys
from pathlib import Path
csv_path = Path("data/ym_R_samples.csv")
out_path = Path("ALSTAR/Models/YMData.lean")
rows = []
with csv_path.open() as f:
r = csv.DictReader(f)
for row in r:
n = int(row["n"])
R = float(row["R"])
rows.append((n, R))
rows.sort()
lines = []
lines.append("import Mathlib.Data.Real.Basic")
lines.append("import ALSTAR.Theorems.TwoBubbleLowerBound")
lines.append("")
lines.append("universe u")
lines.append("")
lines.append("namespace ALSTAR")
lines.append("namespace YMData")
lines.append("")
lines.append("def RTable : List (Nat × Real) :=")
if rows:
lines.append(" [")
for i,(n,R) in enumerate(rows):
comma = "," if i+1 < len(rows) else ""
lines.append(f" ({n}, ({R} : Real)){comma}")
lines.append(" ]")
else:
lines.append(" []")
lines.append("")
lines.append("def R (n : Nat) : Real :=")
lines.append(" match (RTable.find? (fun p => p.1 = n)) with")
lines.append(" | some p => p.2")
lines.append(" | none => 0")
lines.append("")
lines.append("def Schema : TwoBubbleLowerBound.Schema Unit where")
lines.append(" R := R")
lines.append("")
lines.append("end YMData")
lines.append("end ALSTAR")
out_path.write_text("\n".join(lines) + "\n")
