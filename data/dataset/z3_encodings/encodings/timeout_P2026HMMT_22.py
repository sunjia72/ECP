from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import And, Or, Real, Solver

def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])

def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]

def cross(u, v):
    return u[0] * v[1] - u[1] * v[0]

def sqdist(p, q):
    d = sub(p, q)
    return dot(d, d)

def main() -> None:
    pts = [(Real(f'{name}x'), Real(f'{name}y')) for name in ['H', 'O', 'R', 'S', 'E']]
    h, o, r, s, e = pts
    solver = Solver()
    solver.add(sqdist(h, o) == 400, sqdist(s, e) == 676, sqdist(o, s) == 100)
    solver.add(dot(sub(e, h), sub(o, h)) == 0)
    solver.add(dot(sub(o, r), sub(s, r)) == 0)
    solver.add(dot(sub(s, e), sub(h, e)) == 0)
    solver.add(2 * dot(sub(h, o), sub(r, o)) * dot(sub(h, o), sub(r, o)) == sqdist(h, o) * sqdist(r, o))
    solver.add(dot(sub(h, o), sub(r, o)) < 0)
    solver.add(2 * dot(sub(r, s), sub(e, s)) * dot(sub(r, s), sub(e, s)) == sqdist(r, s) * sqdist(e, s))
    solver.add(dot(sub(r, s), sub(e, s)) < 0)
    signed2 = h[0] * o[1] - h[1] * o[0] + o[0] * r[1] - o[1] * r[0] + r[0] * s[1] - r[1] * s[0] + s[0] * e[1] - s[1] * e[0] + e[0] * h[1] - e[1] * h[0]
    print_solver_result(solver, signed2)
if __name__ == '__main__':
    main()
