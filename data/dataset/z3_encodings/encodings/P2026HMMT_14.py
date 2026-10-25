from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from fractions import Fraction
from itertools import product
from z3 import Int, Solver, sat

def main() -> None:
    total = Fraction(0, 1)
    count = 0
    marker = Int('marker')
    domains = [range(i + 1) for i in range(5)]
    for idx, choice in enumerate(product(*domains)):
        weight = Fraction(1, 1)
        for c in choice:
            if c == 0:
                weight *= Fraction(1, 2)
        solver = Solver()
        solver.add(marker == idx)
        if check_solver(solver) == sat:
            total += weight
            count += 1
    print_result(total / count)
if __name__ == '__main__':
    main()
