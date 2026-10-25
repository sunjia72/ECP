from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import Q, Real, Solver, sat
from common import rat_value, check_solver, print_result, require_sat

def main() -> None:
    c, s = (Real('c'), Real('s'))
    solver = Solver()
    solver.add(c > 0, s > 0, c * c + s * s == 1)
    solver.add((2 - c) * (2 - c) + s * s == Q(16, 9))
    if not require_sat(solver):
        return
    c_value = rat_value(solver.model(), c)
    answer = c_value.numerator + c_value.denominator
    print_result(answer)
if __name__ == '__main__':
    main()
