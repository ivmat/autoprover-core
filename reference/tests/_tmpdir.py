"""Shared test helper: a unittest.TestCase subclass that gives each test
method its own temp directory, cleaned up automatically. Not itself a
test module (no `Test*` classes here) - it is imported by the ones that
need scratch space."""

from __future__ import annotations

import contextlib
import shutil
import tempfile
import unittest
from pathlib import Path


class TempDirCase(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.mkdtemp(prefix="autoprover_ref_test_")
        self.addCleanup(shutil.rmtree, self._tmp, ignore_errors=True)

    def tmp_path(self, name: str) -> Path:
        return Path(self._tmp) / name

    @staticmethod
    @contextlib.contextmanager
    def temp_dir():
        d = tempfile.mkdtemp(prefix="autoprover_ref_test_")
        try:
            yield d
        finally:
            shutil.rmtree(d, ignore_errors=True)
