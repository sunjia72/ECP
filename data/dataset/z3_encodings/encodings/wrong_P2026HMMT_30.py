from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import print_solver_result
from z3 import Real, Solver

def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]

def sub(p, q):
    return (p[0] - q[0], p[1] - q[1])

def sqdist(p, q):
    return dot(sub(p, q), sub(p, q))

def main() -> None:
    u, v, ox, oy, hx, hy, lam = Reals = [Real(n) for n in ['u', 'v', 'ox', 'oy', 'hx', 'hy', 'lam']]
    A, B, C = ((0, 0), (11, 0), (u, v))
    G, O, H = (((u + 11) / 3, v / 3), (ox, oy), (hx, hy))
    solver = Solver()
    solver.add(v != 0)
    solver.add(sqdist(A, B) == 121, sqdist(A, C) == 169)
    solver.add(sqdist(O, A) == sqdist(O, B), sqdist(O, A) == sqdist(O, C))
    solver.add(dot(sub(H, A), sub(G, O)) == 0)
    solver.add(dot(sub(H, G), sub(A, O)) == 0)
    solver.add(dot(sub(H, O), sub(A, G)) == 0)
    solver.add(hx == B[0] + lam * (C[0] - B[0]), hy == B[1] + lam * (C[1] - B[1]))
    bc_squared = sqdist(B, C)
    print_solver_result(solver, bc_squared)
if __name__ == '__main__':
    main()
