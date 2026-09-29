#!/usr/bin/env python3
"""Proof-integrity check for the PerronVariational library.

Fails (exit 1) if any `.lean` file under `PerronVariational/` or the root `PerronVariational.lean`

* contains `sorry`, `admit`, an `axiom` declaration, or `native_decide` outside comments and
  strings, or
* is not a Lean module (its first token, after comments, must be `module`).

With `--build-log FILE`, additionally fails if the Lake build log reports
`declaration uses 'sorry'` anywhere (this catches sorries that do not appear in the source text,
e.g. ones introduced by elaboration).

Usage:
    scripts/check_integrity.py [--build-log FILE]
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "PerronVariational"
ROOT_MODULE = ROOT / "PerronVariational.lean"
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide)\b")
MODULE = re.compile(r"^\s*module\b")
LOG_SORRY = re.compile(r"declaration uses [`']sorry[`']")


def code_mask(src: str) -> str:
    """Blank out comments and string literals, keeping the line structure."""
    out, i, depth, state = list(src), 0, 0, "code"
    while i < len(src):
        if state == "code":
            if src.startswith("--", i):
                state = "line"
                continue
            if src.startswith("/-", i):
                state, depth = "block", 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if src[i] == '"':
                state = "str"
                out[i] = " "
            i += 1
        elif state == "line":
            if src[i] == "\n":
                state = "code"
            else:
                out[i] = " "
            i += 1
        elif state == "block":
            if src.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                if depth == 0:
                    state = "code"
            else:
                if src[i] != "\n":
                    out[i] = " "
                i += 1
        else:  # string literal
            if src[i] == "\\":
                out[i] = " "
                if i + 1 < len(src) and src[i + 1] != "\n":
                    out[i + 1] = " "
                i += 2
                continue
            if src[i] == '"':
                state = "code"
            if src[i] != "\n":
                out[i] = " "
            i += 1
    return "".join(out)


def first_code_token_is_module(code: str) -> bool:
    for line in code.splitlines():
        if line.strip():
            return bool(MODULE.match(line))
    return False


def main(argv: list[str]) -> int:
    bad: list[str] = []
    files = sorted(SRC.rglob("*.lean")) + ([ROOT_MODULE] if ROOT_MODULE.exists() else [])
    for path in files:
        raw = path.read_text()
        masked = code_mask(raw)
        rel = path.relative_to(ROOT)
        if not first_code_token_is_module(masked):
            bad.append(f"{rel}: not a Lean module (first token must be `module`)")
        lines = raw.splitlines()
        for n, cl in enumerate(masked.splitlines()):
            if m := FORBIDDEN.search(cl):
                bad.append(f"{rel}:{n + 1}: forbidden `{m.group(1)}`: {lines[n].strip()}")
    if "--build-log" in argv:
        log = Path(argv[argv.index("--build-log") + 1])
        for n, line in enumerate(log.read_text(errors="replace").splitlines()):
            if LOG_SORRY.search(line):
                bad.append(f"{log}:{n + 1}: {line.strip()}")
    print(f"checked {len(files)} files")
    if bad:
        print("VIOLATIONS:")
        for b in bad:
            print("  " + b)
        return 1
    print("OK: no sorry/admit/axiom/native_decide; every file is a module")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
