from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import Int, Solver, sat
from common import divisors, check_solver, print_result, require_sat

def main() -> None:
    total = 0
    marker = Int('n')
    for n in range(1, 500):
        ds = divisors(n)
        predicate = n > 0 and len(ds) >= 6 and (6 in ds) and (sum((d > 6 for d in ds)) == 5)
        solver = Solver()
        solver.add(marker == n, predicate)
        if check_solver(solver) == sat:
            total += n
    print_result(total)
if __name__ == '__main__':
    main()
