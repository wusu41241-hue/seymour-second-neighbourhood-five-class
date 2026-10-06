"""Exact certificates for the incoming-pattern inequalities of every small core.

Uses the already installed local z3 runtime only when a uniform support fails.
Generated integer vectors are checked without the solver before they are saved.
"""
import argparse
import itertools
import json
import math
import sys
import time
from pathlib import Path

# Optional generation dependency: the standard z3-solver Python package.
# The independent integer verifiers do not import or require this package.
import z3


def graph(n, code):
    out = [0] * n
    inc = [0] * n
    for a in range(n):
        for b in range(a + 1, n):
            digit, code = code % 3, code // 3
            if digit == 1:
                out[a] |= 1 << b
                inc[b] |= 1 << a
            elif digit == 2:
                out[b] |= 1 << a
                inc[a] |= 1 << b
    return out, inc


def pattern_rows(inc):
    patterns = set()
    for whole in inc:
        sub = whole
        while sub:
            patterns.add(sub)
            sub = (sub - 1) & whole
    rows = []
    for sub in sorted(patterns):
        incoming = 0
        for v, mask in enumerate(inc):
            if sub & (1 << v):
                incoming |= mask
        rows.append((sub, incoming & ~sub))
    return rows


def valid(weights, rows):
    return any(weights) and all(w >= 0 for w in weights) and all(
        sum(w for i, w in enumerate(weights) if r & (1 << i))
        >= sum(w for i, w in enumerate(weights) if p & (1 << i))
        for p, r in rows
    )


def run(n, target):
    started = time.monotonic()
    variables = [z3.Real(f"core_lambda_{i}") for i in range(n)]
    supports = sorted(range(1, 1 << n), key=lambda s: (s.bit_count(), s))
    certificates = []
    solver_calls = 0
    uniform = 0
    checked_rows = 0
    largest_entry = 0
    nonuniform_examples = []
    total = 3 ** (n * (n - 1) // 2)
    for code in range(total):
        out, inc = graph(n, code)
        rows = pattern_rows(inc)
        checked_rows += len(rows)
        weights = None
        for support in supports:
            if all((r & support).bit_count() >= (p & support).bit_count() for p, r in rows):
                weights = [int(bool(support & (1 << i))) for i in range(n)]
                uniform += 1
                break
        if weights is None:
            solver_calls += 1
            solver = z3.SolverFor("QF_LRA")
            solver.add(*[x >= 0 for x in variables], z3.Sum(variables) == 1)
            for p, r in rows:
                solver.add(z3.Sum([variables[i] for i in range(n) if r & (1 << i)])
                           >= z3.Sum([variables[i] for i in range(n) if p & (1 << i)]))
            answer = solver.check()
            if answer != z3.sat:
                raise RuntimeError(json.dumps({"status": str(answer), "n": n, "code": code, "out": out, "rows": rows}))
            model = solver.model()
            values = [model.eval(x, model_completion=True) for x in variables]
            denominator = math.lcm(*[x.denominator_as_long() for x in values])
            weights = [x.numerator_as_long() * (denominator // x.denominator_as_long()) for x in values]
            divisor = math.gcd(*weights)
            weights = [w // divisor for w in weights]
            if len(nonuniform_examples) < 5:
                nonuniform_examples.append({"code": code, "out": out, "weights": weights})
        if not valid(weights, rows):
            raise RuntimeError(f"Exact independent integer check failed at {n=} {code=}")
        certificates.append(weights)
        largest_entry = max(largest_entry, max(weights))
        if (code + 1) % 10000 == 0:
            print(json.dumps({"n": n, "completed": code + 1, "total": total, "solver_calls": solver_calls}), flush=True)
    artifact = {"n": n, "encoding": "Lexicographic unordered pairs; ternary digit 0 missing, 1 lower->upper, 2 upper->lower; least significant digit first.",
                "condition": "For every P contained in an in-neighborhood, weight(N^-(P) minus P) >= weight(P).",
                "certificates": certificates}
    with target.open("w", encoding="utf-8") as output:
        json.dump(artifact, output, separators=(",", ":"))
        output.write("\n")
    result = {"status": "PASS", "n": n, "graphs": total, "uniform_support_certificates": uniform,
              "exact_LRA_calls": solver_calls, "inequalities_checked": checked_rows,
              "maximum_integer_entry": largest_entry, "nonuniform_examples": nonuniform_examples,
              "certificate_file": str(target), "elapsed_seconds": round(time.monotonic() - started, 3),
              "scope": "Exact small CORE certificate enumeration. The arbitrary-order graph theorem requires a separate proof of the incoming-pattern transfer lemma."}
    print(json.dumps(result, ensure_ascii=False), flush=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, required=True)
    args = parser.parse_args()
    if not 1 <= args.n <= 6:
        raise ValueError("This bounded audit supports core orders one through six only.")
    folder = Path(__file__).resolve().parent
    result = run(args.n, folder / f"incoming_core_certificates_n{args.n}.json")
    with (folder / f"incoming_core_search_n{args.n}.results.json").open("w", encoding="utf-8") as output:
        json.dump(result, output, ensure_ascii=False, indent=2)
        output.write("\n")
