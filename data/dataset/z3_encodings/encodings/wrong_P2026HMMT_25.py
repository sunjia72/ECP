from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import And, Or, Real, Solver

def line_value(line, point):
    a, b, c = line
    x, y = point
    return a * x + b * y + c

def main() -> None:
    centers = [(Real(f'cx_{i}'), Real(f'cy_{i}')) for i in range(3)]
    lines = [(Real(f'la_{i}'), Real(f'lb_{i}'), Real(f'lc_{i}')) for i in range(3)]
    solver = Solver()
    for x, y in centers:
        solver.add(x * x + y * y == 81)
    for a, b, c in lines:
        solver.add(a * a + b * b == 1, c * c < 121)
    incidences = [(0, 0), (0, 1), (1, 1), (1, 2), (2, 2), (2, 0)]
    for line_idx, center_idx in incidences:
        v = line_value(lines[line_idx], centers[center_idx])
        solver.add(Or(v == 2, v == -2))
    solver.add(121 - lines[0][2] ** 2 == 120)
    solver.add(121 - lines[1][2] ** 2 == 120)
    chord_squared = 4 * (121 - lines[2][2] ** 2)
    print_solver_result(solver, chord_squared)
if __name__ == '__main__':
    main()
