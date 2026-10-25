from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from fractions import Fraction
from z3 import Real, Solver, sat
from common import rat_value, check_solver, print_result, require_sat

def main() -> None:
    x3 = Real('x3')
    solver = Solver()
    solver.add(42 * x3 == -2)
    if not require_sat(solver):
        return
    print_result(rat_value(solver.model(), x3))
if __name__ == '__main__':
    main()
