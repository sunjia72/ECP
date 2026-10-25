from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import Int, Solver, sat

def has_subsequence_2026(n: int) -> bool:
    return '2026' in str(n)

def main() -> None:
    good = []
    marker = Int('n')
    n = 101
    while len(good) < 2:
        solver = Solver()
        solver.add(marker == n, n % 101 == 0, has_subsequence_2026(n))
        if check_solver(solver) == sat:
            good.append(n)
        n += 101
    print_result(good[1])
if __name__ == '__main__':
    main()
