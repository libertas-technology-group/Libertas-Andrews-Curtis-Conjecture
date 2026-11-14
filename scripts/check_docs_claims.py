#!/usr/bin/env python3
"""Check that the numbers stated in docs/claims.rst match the disk.

A documented number that no longer matches the repository is a defect: a reader
acts on it. This script reads the three registry rows and the three corpus rows
that carry a counted value and compares each against the tree.

Exit 0 when every stated value matches, 1 otherwise.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "docs" / "claims.rst"


def stated(pattern: str, text: str) -> int | None:
    match = re.search(pattern, text, re.S)
    return int(match.group(1).replace(",", "")) if match else None


def main() -> int:
    text = CLAIMS.read_text()
    failures: list[str] = []

    modules = len(list((ROOT / "lean").glob("*.lean")))
    theorems = sum(
        1 for p in (ROOT / "lean").glob("*.lean")
        for line in p.read_text(errors="ignore").splitlines() if line.startswith("theorem ")
    )
    lemmas = sum(
        1 for p in (ROOT / "lean").glob("*.lean")
        for line in p.read_text(errors="ignore").splitlines() if line.startswith("lemma ")
    )
    keyword = ("theorem ", "lemma ", "def ", "abbrev ", "instance ", "structure ", "class ", "inductive ")
    declarations = sum(
        1 for p in (ROOT / "lean").glob("*.lean")
        for line in p.read_text(errors="ignore").splitlines() if line.startswith(keyword)
    )
    challenge_lines = len((ROOT / "Challenge.lean").read_text().splitlines())
    challenge_bytes = len((ROOT / "Challenge.lean").read_bytes())
    registered = len(json.loads((ROOT / "comparator.json").read_text())["theorem_names"])

    checks = [
        ("Lean modules", r"\* - Lean modules\s+- ([\d,]+)", modules),
        ("Theorems", r"\* - Theorems\s+- ([\d,]+)", theorems),
        ("Lemmas", r"\* - Lemmas\s+- ([\d,]+)", lemmas),
        ("Challenge lines", r"\* - Challenge module size\s+- ([\d,]+) lines", challenge_lines),
        ("Challenge bytes", r"\* - Challenge module size\s+- [\d,]+ lines, ([\d,]+) bytes", challenge_bytes),
        ("Registered theorems", r"\* - Registered theorems\s+- ([\d,]+)", registered),
    ]

    for label, pattern, measured in checks:
        value = stated(pattern, text)
        if value is None:
            failures.append(f"{label}: no stated value found in docs/claims.rst")
        elif value != measured:
            failures.append(f"{label}: docs say {value}, disk says {measured}")
        else:
            print(f"PASS {label} {measured}")

    pages = len(list((ROOT / "docs").rglob("*.rst")))
    prose = [ROOT / "README.md", *sorted((ROOT / "docs").rglob("*.rst")), ROOT / "CITATION.cff"]
    counted = {"modules": modules, "declarations": declarations,
               "theorems": theorems, "lemmas": lemmas, "pages": pages}
    for path in prose:
        for lineno, line in enumerate(path.read_text(errors="ignore").splitlines(), 1):
            for num, noun in re.findall(r"(\d[\d,]*)\s+(modules|declarations|theorems|lemmas|pages)\b", line):
                measured = counted[noun]
                value = int(num.replace(",", ""))
                if value != measured:
                    failures.append(
                        f"{path.relative_to(ROOT)}:{lineno}: says {value} {noun}, disk says {measured}"
                    )
            for num in re.findall(r"\| Declarations \| ([\d,]+) \|", line):
                value = int(num.replace(",", ""))
                if value != declarations:
                    failures.append(
                        f"{path.relative_to(ROOT)}:{lineno}: declarations row says {value}, disk says {declarations}"
                    )
    print(f"PASS prose counts {modules} modules {declarations} declarations {pages} pages")

    if failures:
        for f in failures:
            print("FAIL", f)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
