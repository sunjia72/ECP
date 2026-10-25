from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from itertools import product
from z3 import And, Bool, If, Or, Real, Solver

def main() -> None:
    coords = [(1.0, 0.0), (0.809017, 0.587785), (0.309017, 0.951057), (-0.309017, 0.951057), (-0.809017, 0.587785), (-1.0, 0.0), (-0.809017, -0.587785), (-0.309017, -0.951057), (0.309017, -0.951057), (0.809017, -0.587785)]
    vertices = [(x, y, z) for (x, y), z in product(coords, [0, 1])]
    a, b, c, off = (Real('a'), Real('b'), Real('c'), Real('off'))
    chosen = [Bool(f'chosen_{i}') for i in range(len(vertices))]
    solver = Solver()
    solver.add(Or(a != 0, b != 0, c != 0))
    for bit, (x, y, z) in zip(chosen, vertices):
        value = a * x + b * y + c * z
        solver.add(value != off)
        solver.add(bit == (value < off))
    solver.add(sum((If(bit, 1, 0) for bit in chosen)) == 10)
    print_solver_result(solver)
if __name__ == '__main__':
    main()
