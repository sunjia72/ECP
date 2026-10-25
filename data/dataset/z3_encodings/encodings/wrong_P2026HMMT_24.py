from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import Real, Solver

def sqdist(p, q):
    return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2

def main() -> None:
    a, t, ell2 = (Real('a'), Real('t'), Real('ell2'))
    A, B, C, X, Y = ((0, a), (0, 0), (12, 0), (4, 0), (9, 0))
    T = (12 * t, a * (1 - t))
    solver = Solver()
    solver.add(a > 0, t >= 0, t <= 1)
    solver.add(sqdist(T, A) == ell2, sqdist(T, X) == ell2, sqdist(T, Y) == ell2)
    print_solver_result(solver, ell2)
if __name__ == '__main__':
    main()
