from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from math import comb
from common import check_solver, print_result, require_sat
from z3 import Int, Solver, sat

def main() -> None:
    total = 0
    for k in range(2027):
        total = (total + k * comb(2 * k, k) * pow(2, k, 2027)) % 2027
    answer = Int('answer')
    solver = Solver()
    solver.add(answer == total)
    if not require_sat(solver):
        return
    print_result(solver.model().eval(answer).as_long())
if __name__ == '__main__':
    main()
