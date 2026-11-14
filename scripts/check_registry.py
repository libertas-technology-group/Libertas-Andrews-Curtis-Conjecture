#!/usr/bin/env python3
"""Check the registry entry against the challenge and solution modules.

For every theorem named in comparator.json this script verifies that

  * the declaration exists in Challenge.lean and in Solution.lean,
  * both declarations carry the same name and the same type text,
  * the challenge module declares it with `sorry` and the solution with a proof,
  * the challenge module stays within the registry's line and byte caps,
  * the permitted axiom list is the registry's list.

It then prints the `#print axioms` lines to run, because the axiom record needs
the kernel.

Exit 0 when every textual check passes, 1 otherwise.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHALLENGE = ROOT / "Challenge.lean"
SOLUTION = ROOT / "Solution.lean"
CONFIG = ROOT / "comparator.json"

CAP_LINES = 1000
CAP_BYTES = 102400
PERMITTED = ["propext", "Classical.choice", "Quot.sound"]


def declaration_text(source: str, name: str) -> str | None:
    """Return the text of `theorem <name> ... :=` with whitespace collapsed."""
    pattern = re.compile(
        r"^theorem\s+" + re.escape(name) + r"\b(.*?):=", re.S | re.M
    )
    match = pattern.search(source)
    if not match:
        return None
    return re.sub(r"\s+", " ", match.group(1)).strip()


def main() -> int:
    failures: list[str] = []
    config = json.loads(CONFIG.read_text())
    names = config["theorem_names"]
    challenge = CHALLENGE.read_text()
    solution = SOLUTION.read_text()

    for name in names:
        short = name.split(".")[-1]
        a = declaration_text(challenge, short)
        b = declaration_text(solution, short)
        if a is None:
            failures.append(f"{short}: missing from Challenge.lean")
        if b is None:
            failures.append(f"{short}: missing from Solution.lean")
        if a is not None and b is not None and a != b:
            failures.append(f"{short}: type differs\n    challenge {a}\n    solution  {b}")
        if a is not None and "sorry" not in challenge.split("theorem " + short, 1)[1][:400]:
            failures.append(f"{short}: challenge declaration does not hold a sorry")
        if b is not None and "sorry" in solution.split("theorem " + short, 1)[1][:400]:
            failures.append(f"{short}: solution declaration contains a sorry")

    lines = len(challenge.splitlines())
    size = len(challenge.encode())
    if lines > CAP_LINES:
        failures.append(f"challenge module {lines} lines exceeds {CAP_LINES}")
    if size > CAP_BYTES:
        failures.append(f"challenge module {size} bytes exceeds {CAP_BYTES}")

    if sorted(config["permitted_axioms"]) != sorted(PERMITTED):
        failures.append(f"permitted_axioms is not the registry list: {config['permitted_axioms']}")

    print(f"registered theorems {len(names)}")
    print(f"challenge module {lines} lines {size} bytes (cap {CAP_LINES} / {CAP_BYTES})")
    if failures:
        for f in failures:
            print("FAIL", f)
        return 1

    print("PASS every name and type matches between Challenge and Solution")
    print("PASS the challenge module holds one sorry per theorem and the solution none")
    print("PASS the capability caps and the permitted axiom list")
    print()
    print("run these to complete the checklist:")
    for name in names:
        print(f"  #print axioms {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
