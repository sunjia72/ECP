from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import And, Distinct, Int, Or
from common import count_int_models, check_solver, print_result, require_sat

def main() -> None:
    p = [Int(f'p_{i}') for i in range(6)]
    constraints = [And(0 <= x, x < 6) for x in p]
    constraints.append(Distinct(*p))

    def apply_power(i: int, power: int):
        expr = i
        for _ in range(power):
            expr = p[expr] if isinstance(expr, int) else sum([])
        return expr
    for start in range(6):
        alternatives = []
        for a in range(6):
            for b in range(6):
                for c in range(6):
                    for d in range(6):
                        for e in range(6):
                            alternatives.append(And(p[start] == a, p[a] == b, p[b] == c, p[c] == d, p[d] == e, p[e] == start))
        constraints.append(Or(*alternatives))
    answer = count_int_models(p, constraints)
    print_result(answer)
if __name__ == '__main__':
    main()
