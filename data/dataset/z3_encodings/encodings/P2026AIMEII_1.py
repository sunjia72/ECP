from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import Int, Solver, sat

def main() -> None:
    total = 0
    i, j = (Int('i'), Int('j'))
    for d in [1, 2, 4, 5, 10, 20]:
        solver = Solver()
        solver.add(i >= 0, j >= 0, 4 + i * d == 24, 4 + j * d == 34)
        if check_solver(solver) == sat:
            total += 4 + 9 * d
    print_result(total)
if __name__ == '__main__':
    main()
