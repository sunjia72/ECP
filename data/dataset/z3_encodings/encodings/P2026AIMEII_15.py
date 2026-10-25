from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import And, Int
from common import count_int_models, check_solver, print_result, require_sat

def main() -> None:
    b = [Int(f'b_{i}') for i in range(7)]
    triples = [(0, 1, 3), (1, 2, 4), (2, 3, 5), (3, 4, 6), (4, 5, 0), (5, 6, 1), (6, 0, 2)]
    constraints = [And(1 <= x, x <= 3) for x in b]
    constraints.append(sum(b) % 3 == 0)
    constraints.append(sum((b[i] * b[j] * b[k] for i, j, k in triples)) % 3 == 0)
    answer = count_int_models(b, constraints)
    print_result(answer)
if __name__ == '__main__':
    main()
