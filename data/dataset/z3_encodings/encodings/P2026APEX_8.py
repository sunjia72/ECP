from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from itertools import combinations
from z3 import And, Int
from common import count_int_models, check_solver, print_result, require_sat
ROWS, COLS = (4, 6)
CELLS = [(r, c) for r in range(ROWS) for c in range(COLS)]
CELL_INDEX = {cell: i for i, cell in enumerate(CELLS)}

def all_l_triominoes():
    tiles = []
    for r in range(ROWS - 1):
        for c in range(COLS - 1):
            block = [(r, c), (r + 1, c), (r, c + 1), (r + 1, c + 1)]
            for missing in block:
                tiles.append(tuple(sorted((cell for cell in block if cell != missing))))
    return list(dict.fromkeys(tiles))
TILES = all_l_triominoes()
BY_CELL = {cell: [] for cell in CELLS}
for i, tile in enumerate(TILES):
    for cell in tile:
        BY_CELL[cell].append(i)

def neighboring(tile_a, tile_b) -> bool:
    set_b = set(tile_b)
    for r, c in tile_a:
        if (r + 1, c) in set_b or (r - 1, c) in set_b or (r, c + 1) in set_b or ((r, c - 1) in set_b):
            return True
    return False

def coloring_count(chosen: list[int]) -> int:
    colors = [Int(f'color_{i}') for i in range(len(chosen))]
    constraints = [And(0 <= color, color < 3) for color in colors]
    for i, j in combinations(range(len(chosen)), 2):
        if neighboring(TILES[chosen[i]], TILES[chosen[j]]):
            constraints.append(colors[i] != colors[j])
    return count_int_models(colors, constraints)

def main() -> None:
    covered = [False] * len(CELLS)
    chosen: list[int] = []
    total = 0

    def backtrack() -> None:
        nonlocal total
        try:
            first_uncovered = next((i for i, value in enumerate(covered) if not value))
        except StopIteration:
            total += coloring_count(chosen)
            return
        cell = CELLS[first_uncovered]
        for tile_idx in BY_CELL[cell]:
            indices = [CELL_INDEX[c] for c in TILES[tile_idx]]
            if all((not covered[i] for i in indices)):
                for i in indices:
                    covered[i] = True
                chosen.append(tile_idx)
                backtrack()
                chosen.pop()
                for i in indices:
                    covered[i] = False
    backtrack()
    print_result(total)
if __name__ == '__main__':
    main()
