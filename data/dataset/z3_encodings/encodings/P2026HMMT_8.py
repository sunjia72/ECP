from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import Int, Solver, sat
MOD = 397

def main() -> None:
    values = [1]
    for _ in range(2026):
        prev = values[-1]
        inv = pow((prev + 1) ** 2, -1, MOD)
        values.append(prev * inv % MOD)
    solver = Solver()
    total = Int('total')
    solver.add(values[-1] == 9, total == sum(values) % MOD)
    if not require_sat(solver):
        return
    print_result(solver.model().eval(total).as_long())
if __name__ == '__main__':
    main()
