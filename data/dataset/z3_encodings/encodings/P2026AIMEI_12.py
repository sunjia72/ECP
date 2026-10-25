from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from fractions import Fraction
from z3 import Real, Solver, sat
from common import rat_value, check_solver, print_result, require_sat

def main() -> None:
    z = Real('z')
    ax, ay, az = (0, 0, 1)
    bx, by, bz = (6, 0, 2)
    cx, cy, cz = (0, 4, 3)
    dx, dy, dz = (Fraction(42, 13), Fraction(124, 39), z)
    det = (bx - ax) * ((cy - ay) * (dz - az) - (cz - az) * (dy - ay)) - (by - ay) * ((cx - ax) * (dz - az) - (cz - az) * (dx - ax)) + (bz - az) * ((cx - ax) * (dy - ay) - (cy - ay) * (dx - ax))
    solver = Solver()
    solver.add(det == 0)
    if not require_sat(solver):
        return
    z_value = rat_value(solver.model(), z)
    answer = z_value.numerator + z_value.denominator
    print_result(answer)
if __name__ == '__main__':
    main()
