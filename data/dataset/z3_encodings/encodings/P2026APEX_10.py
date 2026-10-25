from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'helper'))
from functools import lru_cache
from z3 import And, Int
from common import count_int_models, check_solver, print_result, require_sat
TRIPLES = {(0, 1, 2), (1, 2, 0), (2, 0, 1)}

def generate_sequences(counts=(5, 5, 5), prev=None, seq=()):
    if sum(counts) == 0:
        yield seq
        return
    for value in range(3):
        if counts[value] and value != prev:
            next_counts = list(counts)
            next_counts[value] -= 1
            yield from generate_sequences(tuple(next_counts), value, seq + (value,))

@lru_cache(None)
def reducible(seq: tuple[int, ...]) -> bool:
    if not seq:
        return True
    for i in range(len(seq) - 2):
        if seq[i:i + 3] in TRIPLES and reducible(seq[:i] + seq[i + 3:]):
            return True
    return False

def main() -> None:
    accepted = list(generate_sequences())
    vars_ = [Int(f's_{i}') for i in range(15)]
    domain = [And(0 <= v, v < 3) for v in vars_]
    count_constraints = [sum((v == color for v in vars_)) == 5 for color in range(3)]
    adjacent_constraints = [vars_[i] != vars_[i + 1] for i in range(14)]
    count = 0
    for seq in accepted:
        if not reducible(seq):
            continue
        constraints = domain + count_constraints + adjacent_constraints + [vars_[i] == seq[i] for i in range(15)]
        count += count_int_models(vars_, constraints)
    print_result(count)
if __name__ == '__main__':
    main()
