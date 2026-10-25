from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from fractions import Fraction
from itertools import product
from z3 import Int, Solver, sat

def score(seq) -> int:
    seen = set()
    total = 0
    for face in seq:
        if face not in seen:
            total += face + 1
            seen.add(face)
    return total

def main() -> None:
    total = 0
    marker = Int('marker')
    for idx, seq in enumerate(product(range(4), repeat=4)):
        solver = Solver()
        solver.add(marker == idx)
        if check_solver(solver) == sat:
            total += score(seq)
    print_result(Fraction(total, 4 ** 4))
if __name__ == '__main__':
    main()
