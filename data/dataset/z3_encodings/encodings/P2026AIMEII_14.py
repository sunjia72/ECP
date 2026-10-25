from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import Int, Solver, sat
from common import positive_compositions, check_solver, print_result, require_sat

def value(xs):
    acc = 0
    for x in xs:
        if acc % 2 == 1 and x % 2 == 0:
            acc -= x
        else:
            acc += x
    return acc

def main() -> None:
    count = 0
    marker = Int('marker')
    for idx, xs in enumerate(positive_compositions(12)):
        solver = Solver()
        solver.add(marker == idx, value(xs) == 0)
        if check_solver(solver) == sat:
            count += 1
    print_result(count)
if __name__ == '__main__':
    main()
