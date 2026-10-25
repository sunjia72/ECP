import requests
import json

# Define the endpoint
url = "http://0.0.0.0:10080/run_code"

# Define the test code


new = """
#!/usr/bin/env python3
import sys
import os

def main():
    # Full path of current Python executable
    python_executable = sys.executable
    print("Python executable:", python_executable)

    # Directory containing the Python executable
    python_dir = os.path.dirname(python_executable)
    print("Python directory:", python_dir)

if __name__ == "__main__":
    main()

"""

payload = {
    "code": """
# logic_generators/code/bnn_count_pysat.py
from typing import Dict, Any, List, Tuple
from pysat.formula import CNF, IDPool
from pysat.pb import PBEnc
from pysat.solvers import Solver

def _lit(var_id: int, pol: bool) -> int:
    # return DIMACS literal for (var_id) with polarity (True => positive, False => negated)
    return var_id if pol else -var_id

def _encode_network(cnf: CNF, pool: IDPool, layers: List[List[Dict[str, Any]]]):

    for layer in layers:
        for neu in layer:
            out_name = str(neu["out"])
            y = pool.id(out_name)

            lits = []
            for vname, pol in neu["inputs"]:
                v = pool.id(str(vname))
                lits.append(_lit(v, pol))

            k = int(neu["k"])

            # reified "at least k" with top var r
            r = pool.id(f"r_{out_name}")
            enc = PBEnc.atleast(lits=lits, bound=k, vpool=pool, top_id=r)
            cnf.extend(enc.clauses)

            # r <-> y  (two clauses)
            cnf.append([-r, y])
            cnf.append([-y, r])

def _encode_hamming_ball(cnf: CNF, pool: IDPool, seed: List[int], eps: int, n_in: int):

    diff_lits = []
    for i in range(n_in):
        xi = pool.id(f"x{i}")
        if int(seed[i]) == 0:
            diff_lits.append(+xi)
        else:
            diff_lits.append(-xi)
    enc = PBEnc.atmost(lits=diff_lits, bound=int(eps), vpool=pool)
    cnf.extend(enc.clauses)

def _encode_flip(cnf: CNF, pool: IDPool, y_seed: int):
    y = pool.id("y")
    if int(y_seed) == 1:
        # y != 1  -> y == 0
        cnf.append([-y])
    else:
        # y != 0  -> y == 1
        cnf.append([+y])

def _block_input_tuple(s: Solver, pool: IDPool, x_vals: List[Tuple[int, bool]]):
    # block only the assignment over input vars
    clause = []
    for i, val in x_vals:
        xi = pool.id(f"x{i}")
        clause.append(-xi if val else +xi)  # (x_i != val)
    s.add_clause(clause)

def solve(instance: Dict[str, Any]) -> int:

    n_in = int(instance["n_in"])
    layers = instance["layers"]
    prop = instance["property"]
    assert prop["type"] == "hamming_flip_count"

    cnf = CNF()
    pool = IDPool()

    # Ensure all input variables exist in pool
    for i in range(n_in):
        pool.id(f"x{i}")

    # Encode network
    _encode_network(cnf, pool, layers)

    # Encode property
    _encode_hamming_ball(cnf, pool, prop["seed"], int(prop["eps"]), n_in)
    _encode_flip(cnf, pool, int(prop["y_seed"]))

    # Count models (distinct inputs): block on x_i only
    count = 0
    with Solver(bootstrap_with=cnf.clauses) as s:
        while s.solve():
            model = s.get_model()
            # read inputs from model
            x_vals = []
            mset = set(model)
            for i in range(n_in):
                xi = pool.id(f"x{i}")
                val = (xi in mset)  # True if variable appears positively
                x_vals.append((i, val))
            _block_input_tuple(s, pool, x_vals)
            count += 1
    return count

""",
    "language": "python"
}

# Send the request
response = requests.post(url, json=payload)

# Parse and pretty-print the response
try:
    result = response.json()
    print(json.dumps(result, indent=2))
    
    # Optional: check if the output is correct
    if result.get("run_result", {}).get("stdout") == "Hello, world!\n":
        print("✅ Sandbox is working correctly.")
    else:
        print("❌ Sandbox responded but did not return expected output.")
except Exception as e:
    print("❌ Failed to parse response or connect to sandbox:", str(e))
