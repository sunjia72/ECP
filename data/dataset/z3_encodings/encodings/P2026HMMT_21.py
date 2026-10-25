from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import Abs, Real, Solver, sat
from common import rat_value, check_solver, print_result, require_sat

def main() -> None:
    yx, yy, zx, zy, area = (Real('yx'), Real('yy'), Real('zx'), Real('zy'), Real('area'))
    solver = Solver()
    solver.add(yx == 5 - (0 - 4), yy == 0 + (5 - 0))
    solver.add(zx == 0 - (0 - 4), zy == 4 + (5 - 0))
    solver.add(yx > 0, yx < 12, yy > 0, yy < 12, zx > 0, zx < 12, zy > 0, zy < 12)
    solver.add(area == Abs(12 * (12 - yy) + 12 * (yy - 0) + yx * (0 - 12)) / 2)
    if not require_sat(solver):
        return
    print_result(rat_value(solver.model(), area))
if __name__ == '__main__':
    main()
