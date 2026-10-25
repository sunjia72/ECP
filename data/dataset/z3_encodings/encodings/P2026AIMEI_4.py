from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import Int, Solver, sat

def representable(n_value: int) -> bool:
    a, b = (Int('a'), Int('b'))
    solver = Solver()
    solver.add(a > 0, b > 0, a != b, a + b + a * b == n_value)
    return check_solver(solver) == sat

def main() -> None:
    answer = sum((1 for n in range(101) if representable(n)))
    print_result(answer)
if __name__ == '__main__':
    main()
