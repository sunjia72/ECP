from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import Real, Solver

def main() -> None:
    x, y, z = (Real('x'), Real('y'), Real('z'))
    solver = Solver()
    solver.add(x > 0, y > 0, z > 0)
    solver.add(x * y * z == 3)
    solver.add((x - y) * (y - z) * (z - x) == 4)
    solver.add((x + y) * (y + z) * (z + x) == 40)
    solver.add(x < 2 / 3)
    print_solver_result(solver)
if __name__ == '__main__':
    main()
