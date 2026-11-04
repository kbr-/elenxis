"""The Python adapter of `spec-tools tests`: which property tests notice each guard of a module.

A guard is a disjunct of the condition of an `if` whose body returns `None` (a refusal). For each
guard, a copy of the module's directory gets that disjunct replaced by `False` and the named tests
run there with pytest. The output's first JSON line lists the tests the test file defines; then one
line per guard: its line, its source text, and the tests that failed. A guard no test fails is one
the tests don't check.

Usage: python_guards.py MODULE TESTFILE TEST...
"""

from __future__ import annotations

import ast
import json
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class Guard:
    line: int
    start: int  # offset of the disjunct in the source
    end: int
    text: str


def _refuses(body: list[ast.stmt]) -> bool:
    return any(isinstance(s, ast.Return) and isinstance(s.value, ast.Constant) and s.value.value is None
               for s in body)


def guards(source: str) -> list[Guard]:
    """Each disjunct of each refusing `if`, in source order."""
    tree = ast.parse(source)
    offsets = [0]
    for line in source.splitlines(keepends=True):
        offsets.append(offsets[-1] + len(line))
    found = []
    for node in ast.walk(tree):
        if isinstance(node, ast.If) and _refuses(node.body):
            parts = node.test.values if isinstance(node.test, ast.BoolOp) and isinstance(node.test.op, ast.Or) else [node.test]
            for part in parts:
                assert part.end_lineno is not None and part.end_col_offset is not None
                start = offsets[part.lineno - 1] + part.col_offset
                end = offsets[part.end_lineno - 1] + part.end_col_offset
                found.append(Guard(part.lineno, start, end, source[start:end]))
    return sorted(found, key=lambda g: g.start)


def mutate(source: str, guard: Guard) -> str:
    """The source with the guard's disjunct made false."""
    return source[:guard.start] + "False" + source[guard.end:]


def failing_tests(directory: Path, test_file: str, tests: list[str]) -> list[str]:
    """The named tests that fail when run in `directory`."""
    result = subprocess.run(
        [sys.executable, "-m", "pytest", "-q", "-p", "no:cacheprovider", "-rf", test_file,
         "-k", " or ".join(tests)],
        cwd=directory, capture_output=True, text=True, timeout=600)
    failed = {line.split("::", 1)[1].split()[0] for line in result.stdout.splitlines()
              if line.startswith("FAILED ") and "::" in line}
    return [t for t in tests if t in failed]


def check(module: Path, test_file: str, tests: list[str]) -> list[dict[str, object]]:
    source = module.read_text()

    def one(guard: Guard) -> dict[str, object]:
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "copy"
            shutil.copytree(module.parent, copy, ignore=shutil.ignore_patterns("__pycache__", ".hypothesis"))
            (copy / module.name).write_text(mutate(source, guard))
            return {"line": guard.line, "guard": guard.text,
                    "failed": failing_tests(copy, test_file, tests)}

    with ThreadPoolExecutor() as pool:
        return list(pool.map(one, guards(source)))


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    module, test_file, *tests = argv
    tree = ast.parse(Path(test_file).read_text())
    defined = sorted(node.name for node in tree.body
                     if isinstance(node, ast.FunctionDef) and node.name.startswith("test_"))
    print(json.dumps({"tests": defined}))
    for report in check(Path(module).resolve(), test_file, [t for t in tests if t in defined]):
        print(json.dumps(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
