from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from itertools import combinations
from z3 import Real, Solver, sat

def contains_origin_interior(p, q, r) -> bool:
    a, b, c = (Real('a'), Real('b'), Real('c'))
    solver = Solver()
    solver.add(a > 0, b > 0, c > 0, a + b + c == 1)
    solver.add(a * p[0] + b * q[0] + c * r[0] == 0)
    solver.add(a * p[1] + b * q[1] + c * r[1] == 0)
    return check_solver(solver) == sat

def noncollinear(p, q, r) -> bool:
    return (q[0] - p[0]) * (r[1] - p[1]) - (q[1] - p[1]) * (r[0] - p[0]) != 0

def main() -> None:
    points = [(x, y) for x in range(-4, 5) for y in range(-4, 5) if -4 <= x + y <= 4]
    count = 0
    for p, q, r in combinations(points, 3):
        if noncollinear(p, q, r) and contains_origin_interior(p, q, r):
            count += 1
    print_result(count)
if __name__ == '__main__':
    main()
