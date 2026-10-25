from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from functools import lru_cache
from itertools import permutations
from z3 import Int, Solver, sat
FOUR = 3

@lru_cache(None)
def min_swaps_touching_four(state: tuple[int, ...]) -> int:
    if state == tuple(range(7)):
        return 0
    best = 100
    for i in range(6):
        if state[i + 1] < state[i]:
            nxt = list(state)
            nxt[i], nxt[i + 1] = (nxt[i + 1], nxt[i])
            cost = 1 if state[i] == FOUR or state[i + 1] == FOUR else 0
            best = min(best, cost + min_swaps_touching_four(tuple(nxt)))
    return best

def main() -> None:
    marker = Int('marker')
    count = 0
    for idx, perm in enumerate(permutations(range(7))):
        solver = Solver()
        solver.add(marker == idx, min_swaps_touching_four(tuple(perm)) <= 1)
        if check_solver(solver) == sat:
            count += 1
    print_result(count)
if __name__ == '__main__':
    main()
