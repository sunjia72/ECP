from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import And, Bool, If, Int, Solver

def main() -> None:
    a1, a2, a3 = (Int('a1'), Int('a2'), Int('a3'))
    solver = Solver()
    solver.add(a1 >= 0, a2 >= 0, a3 > 0)
    solver.add(a1 + a2 + a3 <= 80)
    print_solver_result(solver)
if __name__ == '__main__':
    main()
