from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import Int, Real, Solver, sat

def main() -> None:
    possible = []
    for r_value in range(1, 1000):
        x, y, r = (Real('x'), Real('y'), Int('r'))
        solver = Solver()
        solver.add(r == r_value)
        solver.add(2 * y == x * x - 8 * x + 12)
        solver.add((x - 4) * (x - 4) + (y - 39) * (y - 39) == r * r)
        solver.add(x - 4 + (y - 39) * (x - 4) == 0)
        if check_solver(solver) == sat:
            possible.append(r_value)
    print_result(sum(possible))
if __name__ == '__main__':
    main()
