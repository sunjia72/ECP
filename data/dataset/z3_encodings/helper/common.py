from __future__ import annotations

from fractions import Fraction
from math import comb, gcd, isqrt

from z3 import And, Int, Or, Solver, sat


TIMEOUT_MS = 30_000


def configure_solver(solver) -> None:
    solver.set("timeout", TIMEOUT_MS)


def check_solver(solver):
    configure_solver(solver)
    return solver.check()


def print_result(value) -> None:
    print(value)


def print_solver_result(solver, expr=None) -> None:
    status = check_solver(solver)
    if status == sat and expr is not None:
        print(solver.model().eval(expr, model_completion=True))
        return
    print(status)
    if str(status) == "unknown":
        print(solver.reason_unknown())


def require_sat(solver) -> bool:
    status = check_solver(solver)
    if status == sat:
        return True
    print(status)
    if str(status) == "unknown":
        print(solver.reason_unknown())
    return False


def rat_value(model, expr) -> Fraction:
    value = model.eval(expr, model_completion=True)
    text = value.as_decimal(80)
    if text.endswith("?"):
        text = text[:-1]
    if "/" in str(value):
        num, den = str(value).split("/", 1)
        return Fraction(int(num.strip()), int(den.strip()))
    return Fraction(text)


def count_int_models(vars_, constraints) -> int:
    solver = Solver()
    solver.add(*constraints)
    count = 0
    while check_solver(solver) == sat:
        model = solver.model()
        count += 1
        solver.add(Or(*[v != model.eval(v, model_completion=True) for v in vars_]))
    return count


def positive_compositions(total: int):
    if total == 0:
        yield []
        return
    for mask in range(1 << (total - 1)):
        current = 1
        xs = []
        for i in range(total - 1):
            if mask & (1 << i):
                xs.append(current)
                current = 1
            else:
                current += 1
        xs.append(current)
        yield xs


def choose_poly(n, k: int):
    if k == 0:
        return 1
    out = 1
    for i in range(k):
        out *= n - i
    return out


def divisors(n: int) -> list[int]:
    out = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            out.append(d)
            if d * d != n:
                out.append(n // d)
    return sorted(out)
