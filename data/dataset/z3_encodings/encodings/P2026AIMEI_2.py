from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from z3 import And, Int
from common import count_int_models, check_solver, print_result, require_sat

def count_length(length: int) -> int:
    digits = [Int(f'd_{length}_{i}') for i in range(length)]
    constraints = [And(1 <= d, d <= 9) for d in digits]
    constraints += [digits[i] == digits[length - 1 - i] for i in range(length)]
    constraints.append(sum(digits) == 13)
    return count_int_models(digits, constraints)

def main() -> None:
    answer = sum((count_length(length) for length in range(1, 14)))
    print_result(answer)
if __name__ == '__main__':
    main()
