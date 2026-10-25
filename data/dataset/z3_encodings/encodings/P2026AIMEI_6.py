from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from itertools import product
from z3 import And, Int
from common import count_int_models, check_solver, print_result, require_sat

def main() -> None:
    a, b = (Int('a'), Int('b'))
    answer = count_int_models([a, b], [And(0 <= a, a <= 20), And(0 <= b, b <= 20)])
    print_result(answer)
if __name__ == '__main__':
    main()
