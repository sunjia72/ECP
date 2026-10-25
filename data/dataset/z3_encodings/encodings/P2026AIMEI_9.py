from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from fractions import Fraction
from z3 import And, Distinct, Int, Or
from common import count_int_models, check_solver, print_result, require_sat

def sticker_visible(seq, k):
    return And(*[seq[j] != seq[k] for j in range(k + 1, 6)])

def exactly_five_faces(seq):
    return Or(*[And(seq[i] == seq[j], Distinct(*[seq[t] for t in range(6) if t != j])) for i in range(6) for j in range(i + 1, 6)])

def main() -> None:
    seq = [Int(f's_{i}') for i in range(6)]
    domain = [And(0 <= x, x < 6) for x in seq]
    visible = [sticker_visible(seq, 1), sticker_visible(seq, 3), sticker_visible(seq, 5)]
    total = count_int_models(seq, domain + visible)
    favorable = count_int_models(seq, domain + visible + [exactly_five_faces(seq)])
    probability = Fraction(favorable, total)
    answer = probability.numerator + probability.denominator
    print_result(answer)
if __name__ == '__main__':
    main()
