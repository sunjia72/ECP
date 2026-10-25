from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import Int, Optimize, sat

def main() -> None:
    p, q, s = (Int('p'), Int('q'), Int('s'))
    opt = Optimize()
    opt.add(p > 0, q > 0, 50 * p == 29 * q, s == p + q)
    opt.minimize(s)
    if not require_sat(opt):
        return
    answer = opt.model().eval(s).as_long()
    print_result(answer)
if __name__ == '__main__':
    main()
