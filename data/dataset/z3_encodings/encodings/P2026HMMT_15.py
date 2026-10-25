from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from common import check_solver, print_result, require_sat
from z3 import Int, Solver, sat

def main() -> None:
    size = 10
    count = 0
    heights: list[int] = []
    marker = Int('marker')

    def search(a: int, prev_height: int) -> None:
        nonlocal count
        if a == size:
            selected = {(i, b) for i, h in enumerate(heights) for b in range(h)}
            ok = True
            for i in range(size):
                for b in range(size):
                    if ((i, b) in selected) == ((size - 1 - i, size - 1 - b) in selected):
                        ok = False
                        break
                if not ok:
                    break
            solver = Solver()
            solver.add(marker == count, ok)
            if check_solver(solver) == sat:
                count += 1
            return
        for h in range(prev_height + 1):
            heights.append(h)
            search(a + 1, h)
            heights.pop()
    search(0, size)
    print_result(count)
if __name__ == '__main__':
    main()
