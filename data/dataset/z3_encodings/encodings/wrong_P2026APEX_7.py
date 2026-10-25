from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import And, Real, Solver

def main() -> None:
    people, colors = (20, 6)
    mass = [[Real(f'm_{i}_{j}') for j in range(colors)] for i in range(people)]
    cap = Real('cap')
    solver = Solver()
    solver.add(cap > 0)
    for i in range(people):
        solver.add(*[mass[i][j] > 0 for j in range(colors)])
        solver.add(sum((mass[i][j] for j in range(colors))) == 1)
    for color in range(colors):
        load = sum((mass[i][color] for i in range(people) if i % colors == color))
        solver.add(load <= cap)
    print_solver_result(solver)
if __name__ == '__main__':
    main()
