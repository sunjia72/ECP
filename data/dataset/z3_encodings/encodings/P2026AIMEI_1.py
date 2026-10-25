from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from math import gcd
from z3 import And, Real, Solver, sat
from common import rat_value, check_solver, print_result, require_sat

def main() -> None:
    d, p = (Real('d'), Real('p'))
    solver = Solver()
    solver.add(p > 0, p != 0, p + 2 != 0, p + 9 != 0, d * (p + 2) == d * p + p * (p + 2), d * (p + 9) == d * (p + 2) + (p + 2) * (p + 9))
    if not require_sat(solver):
        return
    model = solver.model()
    d_value = rat_value(model, d)
    m, n = (d_value.numerator, d_value.denominator)
    if gcd(m, n) != 1:
        raise SystemExit('fraction was not reduced')
    print_result(m + n)
if __name__ == '__main__':
    main()
