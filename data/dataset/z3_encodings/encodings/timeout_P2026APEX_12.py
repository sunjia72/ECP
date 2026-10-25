from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import And, Distinct, Int, Solver

def main() -> None:
    n = 2025
    missing_col = [Int(f'missing_col_{i}') for i in range(n)]
    solver = Solver()
    solver.add(*[And(0 <= x, x < n) for x in missing_col])
    solver.add(Distinct(*missing_col))
    print_solver_result(solver)
if __name__ == '__main__':
    main()
