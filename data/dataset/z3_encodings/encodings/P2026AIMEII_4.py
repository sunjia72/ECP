from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import If, Int, Solver, sat

def main() -> None:
    n, h, t, o, b = (Int('n'), Int('h'), Int('t'), Int('o'), Int('b'))
    count = 0
    for value in range(1, 1000):
        solver = Solver()
        solver.add(n == value)
        solver.add(h == n / 100, t == n / 10 % 10, o == n % 10)
        solver.add(b == If(h >= t, If(h >= o, h, o), If(t >= o, t, o)) + 1)
        solver.add(h * b * b + t * b + o == n)
        if check_solver(solver) == sat:
            count += 1
    print_result(count)
if __name__ == '__main__':
    main()
