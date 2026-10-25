from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from math import comb
from common import check_solver, print_result, require_sat
from z3 import Int, Solver, sat

def main() -> None:
    good = 0
    r = Int('r')
    for value in range(502):
        total_mod = 0
        for k in range(value, 10001, 502):
            total_mod = (total_mod + comb(10000, k)) % 503
        solver = Solver()
        solver.add(r == value, total_mod == 0)
        if check_solver(solver) == sat:
            good += 1
    print_result(good)
if __name__ == '__main__':
    main()
