#!/usr/bin/env python3
"""Convenience entry point: ``python3 run_tests.py`` (run from
``reference/``) runs the full pure-Python test suite with no environment
variables or installed packages required. Equivalent to:

    PYTHONPATH=. python3 -m unittest discover -s tests -p "test_*.py" -v

Everything under ``reference/tests/`` runs with no Lean installation —
see ``reference/examples/`` for the one place this project does invoke
Lean, kept deliberately separate from the test suite.
"""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main() -> int:
    sys.path.insert(0, str(ROOT))
    loader = unittest.TestLoader()
    suite = loader.discover(str(ROOT / "tests"), pattern="test_*.py")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
