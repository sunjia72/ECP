from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import Int, Solver, sat

def feasible(x_value: int) -> bool:
    x, y, z = (Int('x'), Int('y'), Int('z'))
    solver = Solver()
    solver.add(x == x_value, x > 0, y > 0, z > 0)
    solver.add(y < 2 * x)
    solver.add(z * z * (2 * x + y) == x * y * y)
    solver.add(6 * (2 * x + y) == 125 * (y + 2 * z))
    return check_solver(solver) == sat

def main() -> None:
    for x in range(1, 1000):
        if feasible(x):
            print_result(x)
            return
    raise SystemExit('no feasible x found')
if __name__ == '__main__':
    main()
