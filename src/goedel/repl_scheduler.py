import os
import sys
import time
import json
import ctypes
import resource
import tempfile
import traceback
import threading
import pexpect
import subprocess
import multiprocessing as mp
from pprint import pprint
# from memory_profiler import profile

import random

import numpy as np
import re

def is_effectively_empty_code(code):
    """Return True for missing/placeholder code that should not be sent to Lean."""
    if code is None:
        return True
    if not isinstance(code, str):
        return True
    stripped = code.strip()
    if stripped == "":
        return True
    if stripped.lower() in {"none", "null", "nan"}:
        return True
    return False

def split_list_randomly(lst, k):
    random.shuffle(lst)  # Shuffle the list randomly
    return list(map(list, np.array_split(lst, k)))  # Split into k approximately equal parts


CURRENT_DIR = os.path.dirname(os.path.abspath(__file__))


sys.path.append(os.path.abspath(os.path.join(CURRENT_DIR, "../../")))


IMPORT_TIMEOUT = 100
# PROOF_TIMEOUT = 120
PROOF_TIMEOUT = int(os.environ.get("PROOF_TIMEOUT", 120))

HOME_DIR = os.path.expanduser('~')

DEFAULT_LAKE_PATH = f'{HOME_DIR}/.elan/bin/lake'


DEFAULT_LEAN_WORKSPACE="Formalization"


DEFAULT_IMPORTS = "import Mathlib\nimport Aesop\nopen BigOperators Classical ENNReal Equiv EuclideanGeometry Filter Finset Fintype Function Lex List MeasureTheory Nat ProbabilityTheory Real SimpleGraph Real Nat Topology Rat\nset_option maxHeartbeats 0\n"
# DEFAULT_IMPORTS = "import Mathlib\nimport Aesop\n\nset_option maxHeartbeats 0\n\nopen BigOperators Real Nat Topology Rat\n\n"


statement_sample = "\n/-- Show that $\frac{9x^2\\sin^2 x + 4}{x\\sin x} \\geq 12$ for $0 < x < \\pi$.-/\ntheorem aime_1983_p9 (x : ℝ) (h₀ : 0 < x ∧ x < Real.pi) :\n  12 ≤ (9 * (x ^ 2 * Real.sin x ^ 2) + 4) / (x * Real.sin x) :="

proof_code_sample_1 = " by\n  /-\n  To find the minimum value of $\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$, we need to show that it is at least 12. We start by noting that the expression can be rewritten using the division property of inequalities. We then use the fact that \\$sin x$ and $x$ are positive in the given range to establish the necessary inequalities. Finally, we apply these results to conclude that the minimum value is indeed 12.\n  -/\n  -- We start by ensuring that the product x * sin x is positive in the given range.\n  have h₁ : 0 < x * Real.sin x := by\n    apply mul_pos\n    -- x is positive in the range (0, π).\n    exact h₀.1\n    -- sin x is positive in the range (0, π).\n    exact Real.sin_pos_of_pos_of_lt_pi h₀.1 h₀.2\n  -- Using the division property of inequalities, we rewrite the expression.\n  rw [le_div_iff h₁]\n  /- tactic state:\n    x : ℝ\n    h₀ : 0 < x ∧ x < π\n    h₁ : 0 < x * x.sin\n    ⊢ 12 * (x * x.sin) ≤ 9 * (x ^ 2 * x.sin ^ 2) + 4\n  -/\n  -- This is equivalent to showing that 9x^2 sin^2 x - 12x sin x + 4 ≥ 0, and the left hand side can be rewritten as a perfect square (3x sin x - 2)^2.\n  -- We use the fact that (3x sin x - 2)^2 is non-negative to establish this.\n  nlinarith [sq_nonneg (3 * x * Real.sin x - 2)]\n"

proof_code_sample_2 = " by sorry"

proof_code_sample_3 = "\n/-- For a series $\\{a_n\\}$, we have $\\sum_{n=0}^{99} a_{n+1}^2 = 1$. Show that $\\sum_{n=0}^{98} (a_{n+1}^2 a_{n+2}) + a_{100}^2 * a_1 < \\frac{12}{25}$.-/\ntheorem imosl_2007_algebra_p6 (a : \u2115 \u2192 NNReal) (h\u2080 : (\u2211 x in Finset.range 100, a (x + 1) ^ 2) = 1) :\n    (\u2211 x in Finset.range 99, a (x + 1) ^ 2 * a (x + 2)) + a 100 ^ 2 * a 1 < 12 / 25 := by\n  /-\n  Given a series \\(\\{a_n\\}\\), we know that \\(\\sum_{n=0}^{99} a_{n+1}^2 = 1\\). We need to show that \\(\\sum_{n=0}^{98} (a_{n+1}^2 a_{n+2}) + a_{100}^2 * a_1 < \\frac{12}{25}\\).\n  -/\n  -- Simplify the given sum condition using basic arithmetic properties.\n  simp_all [Finset.sum_range_succ, mul_add, mul_comm, mul_left_comm, mul_assoc, add_assoc,\n    add_left_comm, add_comm]\n  -- Use linear arithmetic to prove the inequality.\n  <;> nlinarith [h\u2080]"

proof_code_sample_4 = "BUG" * 4096

proof_code_sample_5 = DEFAULT_IMPORTS

proof_code_sample_nonneg="\n/-- Suppose $a, b, c$ are the sides of a triangle. Prove that \n\n$a^2(b+c-a)+b^2(c+a-b)+c^2(a+b-c)\\le{3abc}.$-/\ntheorem imo_1964_p2 (a b c : \u211d) (h\u2080 : 0 < a \u2227 0 < b \u2227 0 < c) (h\u2081 : c < a + b) (h\u2082 : b < a + c)\n    (h\u2083 : a < b + c) :\n    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) \u2264 3 * a * b * c := by\n  /-\n  To prove the inequality \\(a^2(b+c-a) + b^2(c+a-b) + c^2(a+b-c) \\leq 3abc\\) for the sides \\(a, b, c\\) of a triangle, we can use the non-negativity of squares and some algebraic manipulations. Specifically, we will use the fact that the square of any real number is non-negative, and then apply these properties to the differences \\(a - b\\), \\(b - c\\), and \\(c - a\\). By leveraging these non-negative terms, we can derive the desired inequality.\n  -/\n  -- Use the non-negativity of squares to derive the inequality.\n  -- Specifically, we use the fact that the square of any real number is non-negative.\n  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),\n    sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b)]"

# proof_code_list_sample = [proof_code_sample] * 1
# proof_code_list_sample = [statement_sample + proof_code_sample_1, statement_sample + proof_code_sample_2] * 2

# proof_code_list_sample = ([{"name": "test_problem", "code": statement_sample + proof_code_sample_1}] + [{"name": "test_problem", "code": statement_sample + proof_code_sample_2}]) * 1

# proof_code_list_sample = [{"name": "test_problem", "code": statement_sample + proof_code_sample_1}] * 1

proof_code_list_sample = [{"name": "nonneg_problem", "code": statement_sample + proof_code_sample_2}]


# proof_code_list_sample.append({'name': 'timeout_problem', 'code': proof_code_sample_3})
# proof_code_list_sample.append({'name': 'timeout_problem', 'code': proof_code_sample_5})

problem_list_sample = [proof_code_list_sample] * 64 #each item in problem_list_sample is a proof_code_list which I want a single process to do

def initiate_child(imports = DEFAULT_IMPORTS, max_retries=3):
    # Start Lean REPL and require a healthy initialization response before returning.
    last_response = None
    for _ in range(max_retries):
        child = pexpect.spawn(f"/bin/bash", cwd=DEFAULT_LEAN_WORKSPACE, encoding='utf-8', maxread=1, echo=False)

        # # Uncomment the next line to see the REPL's output for debugging
        # child.logfile = sys.stdout

        child.sendline("stty -icanon")
        child.sendline(f"{DEFAULT_LAKE_PATH} exe repl")

        response = send_command_and_wait(child, imports, timeout=IMPORT_TIMEOUT)
        last_response = response

        comp = response.get("compilation_result", {})
        healthy = (
            comp.get("system_errors") is None
            and comp.get("pass", False)
            and response.get("env") is not None
        )
        if healthy:
            return child, response

        try:
            child.close()
        except Exception:
            child.terminate(force=True)

    return None, last_response

def send_command_and_wait(child, command, allTactics=False, ast=False, premises=False, tactics=False, env=None, timeout=PROOF_TIMEOUT, imports=DEFAULT_IMPORTS):
    """
    Send a JSON command to the Lean REPL and wait for the output.
    The REPL output is expected to be a JSON dict (possibly spanning multiple lines)
    ending with a double newline.
    """
    # Build the JSON command
    if env is None:
        json_cmd = json.dumps({"cmd": command})
    else:
        json_cmd = json.dumps({"cmd": command, "allTactics" : allTactics, "ast":ast, "premises" : premises, "tactics" : tactics, "env": env})

    child.sendline(json_cmd)
    child.sendline("")  # This sends the extra newline.


    # import pdb; pdb.set_trace()

    code = imports + command
    try:
        # Wait for the output delimiter (double newline)
        child.expect(["\r\n\r\n", "\n\n"], timeout=timeout)
        # pexpect.before contains everything up to the matched delimiter.
        response = child.before.strip()

        block = response
        
        # problem_id = proof_code_list[i]["name"]
        try:
            # Some environments print extra shell/lake logs around REPL JSON.
            # Extract the last JSON object in the captured block if needed.
            block_for_json = block
            try:
                result = json.loads(block_for_json)
            except json.JSONDecodeError:
                json_start_positions = [m.start() for m in re.finditer(r"\{", block_for_json)]
                result = None
                for start in reversed(json_start_positions):
                    candidate = block_for_json[start:].strip()
                    try:
                        result = json.loads(candidate)
                        break
                    except json.JSONDecodeError:
                        continue
                if result is None:
                    raise

            # ast_results = lean4_parser(command, result['ast']) if 'ast' in result and result['ast'] else {}
            ast_results = {}
            parsed_result = {
                "sorries": result.get("sorries", []),
                "tactics": result.get("tactics", []),
                "errors": [m for m in result.get("messages", []) if m.get("severity") == "error"],
                "warnings": [m for m in result.get("messages", []) if m.get("severity") == "warning"],
                "infos": [m for m in result.get("messages", []) if m.get("severity") == "info"],
                "ast" : ast_results,
                # "verified_code": code,
                # "problem_id": problem_id
                "system_errors": None
            }
            parsed_result["pass"] = not parsed_result["errors"]
            parsed_result["complete"] = (
                parsed_result["pass"]
                and not parsed_result["sorries"]
                and not any(
                    "declaration uses 'sorry'" in warning["data"] or "failed" in warning["data"]
                    for warning in parsed_result["warnings"]
                )
            )
            env_out = result.get("env", None)

        except json.JSONDecodeError as e:

            parsed_result = {
                "pass": False,
                "complete": False,
                # "verified_code": code,
                # "problem_id": problem_id,
                "system_errors": f"JSONDECODE ERROR: {e}"
            }
            env_out = None
    
        response = {"code": command, "compilation_result": parsed_result, "env": env_out}


    except pexpect.TIMEOUT as e:
        response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"TIMEOUT ERROR: {e}"}, "env": None}
    except pexpect.EOF as e:
        response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"EOF ERROR: {e}"}, "env": None}
    except Exception as e:  # Catch any other unexpected errors
        response = {"code": command, "compilation_result": {"pass": False, "complete": False, "system_errors": f"UNEXPECTED ERROR: {e}"}, "env": None}
    return response

def worker(worker_id, task_queue, result_list, total_restarts, lock, allTactics=False, ast=False, premises=False, tactics=False, timeout=PROOF_TIMEOUT, imports = DEFAULT_IMPORTS):
    """Worker function that continuously picks tasks and executes them."""
    child, init_response = initiate_child(imports=imports)  # Start Lean 4 REPL
    base_env = init_response.get("env") if init_response else None
    print(f"Worker {worker_id} started Lean REPL.", flush = True)

    start_time = time.time()

    while True:
        try:
            proof_code_dict = task_queue.get(timeout=10)

            proof_code = proof_code_dict["code"]
            proof_name = proof_code_dict["name"]
            # proof_id, proof_command = task_queue.get(timeout=10)  # Get task
        except mp.queues.Empty:
            break  # Exit if no tasks are left


        if child is None:
            response = {
                "code": proof_code,
                "compilation_result": {
                    "pass": False,
                    "complete": False,
                    "system_errors": "REPL INIT ERROR: failed to initialize Lean REPL."
                },
                "env": None,
            }
            response["name"] = proof_name
            response["verify_time"] = round(time.time() - start_time, 2)
            start_time = time.time()
            with lock:
                result_list.append(response)
            continue

        if is_effectively_empty_code(proof_code):


            response = {"code": proof_code, "compilation_result": {"pass": False, "complete": False, "system_errors": None}}

            response["name"] = proof_name

            response["verify_time"] = round(time.time() - start_time, 2)

            start_time = time.time()

            with lock:
                result_list.append(response)

        else:

            response = send_command_and_wait(
                child,
                proof_code,
                allTactics=allTactics,
                ast=ast,
                premises=premises,
                tactics=tactics,
                env=base_env,
                imports=imports,
            )  # Run proof

            response["name"] = proof_name

            response["verify_time"] = round(time.time() - start_time, 2)

            start_time = time.time()

            with lock:
                result_list.append(response)

            if response["compilation_result"]["system_errors"] is not None:


                with total_restarts.get_lock():  # Ensure atomic update
                    total_restarts.value += 1  # Increment total restart count 

                if "EOF" in response["compilation_result"]["system_errors"]:

                    # # debug
                    # print("EOF error:", response["compilation_result"]["system_errors"], flush = True)

                    previous_id = child.pid

                    try:
                        child.close()
                    except Exception:
                        child.terminate(force=True)

                    # with total_restarts.get_lock():  # Ensure atomic update
                    #     total_restarts.value += 1  # Increment total restart count  

                    if task_queue.empty():
                        print(f"Worker {worker_id}: No more proofs left. Not restarting REPL.", flush=True)
                        break  # Exit instead of restarting
                    else:
                        child, init_response = initiate_child(imports=imports)
                        base_env = init_response.get("env") if init_response else None

                    # print("EOF restart", previous_id, "replaced with", child.pid, flush = True) 
                else : 
                    previous_id = child.pid
                    try:
                        child.close()
                    except Exception:
                        child.terminate(force=True)

                    if task_queue.empty():
                        print(f"Worker {worker_id}: No more proofs left. Not restarting REPL.", flush=True)

                        break  # Exit instead of restarting
                    else:
                        child, init_response = initiate_child(imports=imports)
                        base_env = init_response.get("env") if init_response else None

                    # print("restart because of", response["compilation_result"]["system_errors"], previous_id, "replaced with", child.pid, flush = True) 
                    # print("Timemout restart", previous_id, "replaced with", child.pid, flush = True) 


    if child is not None:
        try:
            child.close()
        except Exception:
            child.terminate(force=True)
    print(f"Worker {worker_id} terminated Lean REPL.", flush = True)
    




def scheduler(proofs, num_workers=64, allTactics=False, ast=False, premises=False, tactics=False, timeout = PROOF_TIMEOUT, imports = DEFAULT_IMPORTS):
    # proofs is a list of all the proofs that need to verify

    """Scheduler function that launches REPL processes and assigns tasks to CPUs."""
    task_queue = mp.Queue()
    result_queue = mp.Queue()
    total_restarts = mp.Value('i', 0)  # Shared counter for total REPL restarts


    manager = mp.Manager()
    result_list = manager.list()  #  Shared list
    lock = manager.Lock()  #  Lock for thread safety

    # Populate the task queue
    for proof in proofs:
        task_queue.put(proof)

    # Start worker processes
    workers = []
    for i in range(num_workers):
        # process = mp.Process(target=worker, args=(i, task_queue, result_list, total_restarts, lock))
        process = mp.Process(target=worker, args=(i, task_queue, result_list, total_restarts, lock, allTactics, ast, premises, tactics, timeout, imports))
        process.start()
        workers.append(process)




    # Monitor progress while workers are running
    total_proofs = len(proofs)
    while any(worker.is_alive() for worker in workers):  # While workers are active
        time.sleep(10)  #  Check progress every 10 seconds
        print(f"Progress: {len(result_list)}/{total_proofs} proofs processed. REPL errors: {total_restarts.value}", flush=True)


    # Wait for all processes to finish
    for process in workers:
        # process.join(timeout=60)
        process.join()

    task_queue.close()
    task_queue.join_thread()


    print(f"All proofs processed! Total REPL Errors: {total_restarts.value}", flush = True)

    # print(results, flush = True)

    return list(result_list)






if __name__ == '__main__':


    print(scheduler(proof_code_list_sample, num_workers=16, allTactics=False, ast=False, premises=False, tactics=False))

    # scheduler(proof_code_list_sample, num_workers=1, ast=True)
