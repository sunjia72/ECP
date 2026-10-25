from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import Int, Solver, sat
from common import choose_poly, check_solver, print_result, require_sat

def possible(n_value: int) -> bool:
    r, b = (Int('r'), Int('b'))
    solver = Solver()
    solver.add(r >= 7, b >= 7, r + b == n_value)
    solver.add(5 * choose_poly(r, 4) * choose_poly(b, 3) == 3 * choose_poly(r, 5) * choose_poly(b, 2))
    return check_solver(solver) == sat

def main() -> None:
    found = []
    n = 14
    while len(found) < 5:
        if possible(n):
            found.append(n)
        n += 1
    print_result(sum(found))
if __name__ == '__main__':
    main()
