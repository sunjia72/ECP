from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from itertools import product
from z3 import Int, Solver, sat

def main() -> None:
    primes = [7, 11, 13, 17]
    count = 0
    exps = [Int(f'e_{i}') for i in range(4)]
    for values in product(range(18), repeat=4):
        divisor_mod_12 = 1
        for p, e in zip(primes, values):
            divisor_mod_12 = divisor_mod_12 * pow(p, e, 12) % 12
        solver = Solver()
        solver.add(*[exps[i] == values[i] for i in range(4)])
        solver.add(divisor_mod_12 == 5)
        if check_solver(solver) == sat:
            count += 1
    print_result(count % 1000)
if __name__ == '__main__':
    main()
