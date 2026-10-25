from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from fractions import Fraction
from z3 import And, Int
from common import count_int_models, check_solver, print_result, require_sat

def has_topic(test, topic):
    return sum([test[i] == topic for i in range(4)]) >= 1

def main() -> None:
    test = [Int(f't_{i}') for i in range(4)]
    domain = [And(0 <= x, x < 4) for x in test]
    given = [has_topic(test, 0), has_topic(test, 1), has_topic(test, 2)]
    total = count_int_models(test, domain + given)
    favorable = count_int_models(test, domain + given + [has_topic(test, 3)])
    print_result(Fraction(favorable, total))
if __name__ == '__main__':
    main()
