from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import And, Distinct, Int, Or, Solver

def cell_id(x, y):
    return 3 * x + y

def valid_step(u, v):
    cases = []
    for x1 in range(20):
        for y1 in range(3):
            for x2 in range(20):
                for y2 in range(3):
                    vertical = x1 == x2 and abs(y1 - y2) == 1
                    horizontal = y1 == y2 and x2 == (x1 + 1) % 20
                    if vertical ^ horizontal:
                        cases.append(And(u == cell_id(x1, y1), v == cell_id(x2, y2)))
    return Or(*cases)

def main() -> None:
    path = [Int(f'p_{i}') for i in range(60)]
    solver = Solver()
    solver.add(*[And(0 <= p, p < 60) for p in path])
    solver.add(Distinct(*path))
    solver.add(Or(*[path[0] == cell_id(x, 2) for x in range(20)]))
    solver.add(Or(*[path[-1] == cell_id(x, 0) for x in range(20)]))
    for i in range(59):
        solver.add(valid_step(path[i], path[i + 1]))
    print_solver_result(solver)
if __name__ == '__main__':
    main()
