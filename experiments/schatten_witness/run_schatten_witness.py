import json
from pathlib import Path
from verification.schatten_p_witness import main as build_data

def main():
    build_data()
    path = Path("data/schatten_witness/schatten_p_witness.json")
    rows = json.loads(path.read_text())
    for row in rows:
        print(
            "L=", row["L"],
            "cutoff=", row["cutoff"],
            "W_3_N32=", row["W_3_N32"],
            "W_4_N32=", row["W_4_N32"],
            "W_6_N32=", row["W_6_N32"],
        )

if __name__ == "__main__":
    main()
