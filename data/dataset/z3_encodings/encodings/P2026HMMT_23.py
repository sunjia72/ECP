from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import Abs, Real, Solver, sat
from common import rat_value, check_solver, print_result, require_sat

def main() -> None:
    w, x, y, z, d2 = (Real('w'), Real('x'), Real('y'), Real('z'), Real('d2'))
    solver = Solver()
    solver.add(w >= 0, w <= 12, x >= 0, x <= 16, y >= 0, y <= 12, z >= 0, z <= 16)
    solver.add(w + y == 12, x + z == 16)
    solver.add((12 - w) ** 2 + x ** 2 == (12 - y) ** 2 + (16 - x) ** 2)
    solver.add((12 - y) ** 2 + (16 - x) ** 2 == y ** 2 + (16 - z) ** 2)
    solver.add(y ** 2 + (16 - z) ** 2 == w ** 2 + z ** 2)
    solver.add(Abs((12 - w) * (16 - x) - x * (y - 12)) == 120)
    solver.add(d2 == (12 - y) ** 2 + (16 - x) ** 2)
    if not require_sat(solver):
        return
    print_result(rat_value(solver.model(), d2))
if __name__ == '__main__':
    main()
