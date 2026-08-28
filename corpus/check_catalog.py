#!/usr/bin/env python3
"""Check that ``corpus/CATALOG.md`` still describes the corpus that exists.

Run it from anywhere::

    python3 corpus/check_catalog.py

The catalog is the corpus's navigational index and, in its Scope column, its
honesty column. Both roles decay the same way: a module is added, renamed or
dropped, and the catalog keeps describing the corpus of a month ago. Nothing in
``lake build`` notices, because the catalog is prose. This script is the
noticing.

It asserts three things.

1. The catalog's row set, the import set in ``corpus/AutoproverCorpus.lean``
   and the set of module files under ``corpus/AutoproverCorpus/`` are the same
   set, and each module sits in the same subject area in all three. A module
   the catalog omits is an undocumented claim; a module the catalog invents is
   a claim with no proof behind it; a module missing from the import root is
   never built, so ``lake build`` being green says nothing about it.

2. Every count the catalog states about itself is the count you get by
   counting: the per-area ``N modules.`` footers, and the Total line's area
   count, module count, per-area breakdown, and `full`/`scoped` totals. The
   totals are the numbers a reader is most likely to quote and least likely to
   recount.

3. Every `scoped` row says what is restricted. "scoped" on its own is a flag
   that warns without informing, which is the failure mode the Scope column
   exists to prevent. Every flag must be exactly `full`, or `scoped` followed
   by a non-empty restriction.

Exit status is 0 when every check passes and 1 when any check fails. Failures
are printed one per line, each naming the module or line at fault. Standard
library only, like the rest of this repository.

``--selftest`` is the positive control. A check nobody has watched fail is not
known to be a check at all: it may be passing because the corpus is consistent,
or because the parser quietly matched nothing. ``--selftest`` copies the corpus
to a temporary directory, plants one violation at a time, and requires the
named check to fail on each. It never writes to the real corpus.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
import tempfile
from pathlib import Path

# ``| Module | Proves | Attribution | Scope |`` — a row of the per-area tables.
_TABLE_HEADER = "| Module | Proves | Attribution | Scope |"
_TABLE_RULE = "|---|---|---|---|"

_AREA_HEADING = re.compile(r"^##\s+(?P<area>.+?)\s*$")
_AREA_FOOTER = re.compile(r"^(?P<area>[A-Za-z][A-Za-z ]*):\s+(?P<count>\d+)\s+modules\.\s*$")
_IMPORT = re.compile(r"^import\s+AutoproverCorpus\.(?P<area>\w+)\.(?P<module>\w+)\s*$")
_SCOPED = re.compile(r"^scoped\s*[—-]\s*(?P<restriction>\S.*)$")

_TOTAL = re.compile(
    r"^(?P<areas>\d+)\s+areas,\s+(?P<modules>\d+)\s+modules\s+"
    r"\((?P<breakdown>[^)]*)\);\s+"
    r"(?P<full>\d+)\s+flagged\s+`full`,\s+(?P<scoped>\d+)\s+flagged\s+`scoped`\.\s*$"
)
_BREAKDOWN_ENTRY = re.compile(r"^(?P<area>[A-Za-z][A-Za-z ]*?)\s+(?P<count>\d+)$")

# The Total section is a summary, not a subject area with modules of its own.
_NON_AREA_HEADINGS = {"Total"}


class Row:
    """One catalog row: a module, the area whose table it sits in, its flag."""

    def __init__(self, module: str, area: str, flag: str, lineno: int) -> None:
        self.module = module
        self.area = area
        self.flag = flag
        self.lineno = lineno


class Catalog:
    """What ``CATALOG.md`` says: its rows, its per-area footers, its totals."""

    def __init__(self) -> None:
        self.rows: list[Row] = []
        self.area_order: list[str] = []
        self.footers: dict[str, tuple[int, int]] = {}  # area -> (count, lineno)
        self.total_line: str | None = None
        self.total_lineno: int = 0
        self.malformed: list[str] = []


def parse_catalog(path: Path) -> Catalog:
    """Read ``CATALOG.md`` into a `Catalog`, recording anything unparseable."""
    catalog = Catalog()
    area: str | None = None
    in_total = False

    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.rstrip()

        heading = _AREA_HEADING.match(line)
        if heading:
            name = heading.group("area")
            in_total = name in _NON_AREA_HEADINGS
            area = None if in_total else name
            if area is not None:
                catalog.area_order.append(area)
            continue

        if in_total and line.strip() and not line.startswith("#"):
            if catalog.total_line is None:
                catalog.total_line = line.strip()
                catalog.total_lineno = lineno
            continue

        footer = _AREA_FOOTER.match(line)
        if footer:
            catalog.footers[footer.group("area")] = (int(footer.group("count")), lineno)
            continue

        if not line.startswith("| "):
            continue
        if line == _TABLE_HEADER or line.replace(" ", "") == _TABLE_RULE:
            continue

        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 4:
            catalog.malformed.append(
                f"CATALOG.md:{lineno}: table row has {len(cells)} cells, expected 4: {line[:60]}..."
            )
            continue
        if area is None:
            catalog.malformed.append(
                f"CATALOG.md:{lineno}: table row `{cells[0]}` sits under no `## Area` heading"
            )
            continue
        catalog.rows.append(Row(cells[0], area, cells[3], lineno))

    return catalog


def parse_imports(path: Path) -> tuple[dict[str, str], list[str]]:
    """Read the import root into ``module -> area``, plus any unparseable lines."""
    modules: dict[str, str] = {}
    problems: list[str] = []
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line:
            continue
        match = _IMPORT.match(line)
        if not match:
            problems.append(f"AutoproverCorpus.lean:{lineno}: not an `import AutoproverCorpus.<Area>.<Module>` line: {line}")
            continue
        module = match.group("module")
        if module in modules:
            problems.append(f"AutoproverCorpus.lean:{lineno}: `{module}` is imported twice")
        modules[module] = match.group("area")
    return modules, problems


def scan_files(root: Path) -> tuple[dict[str, str], list[str]]:
    """Read ``corpus/AutoproverCorpus/**/*.lean`` into ``module -> area``."""
    modules: dict[str, str] = {}
    problems: list[str] = []
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        module = path.stem
        area = path.parent.name
        if path.parent == root:
            problems.append(f"{path}: module file sits directly in AutoproverCorpus/, outside any area directory")
            continue
        if module in modules:
            problems.append(f"{path}: a second module file is also named `{module}`")
        modules[module] = area
    return modules, problems


def check_sets(catalog: Catalog, imports: dict[str, str], files: dict[str, str]) -> list[str]:
    """Check 1: catalog rows, imports and module files are the same set."""
    problems: list[str] = []

    seen: set[str] = set()
    rows: dict[str, str] = {}
    for row in catalog.rows:
        if row.module in seen:
            problems.append(f"CATALOG.md:{row.lineno}: `{row.module}` has a second row")
        seen.add(row.module)
        rows[row.module] = row.area

    # Compared pairwise rather than as one three-way set difference, so a
    # failure report names which of the three surfaces disagrees with which.
    for module in sorted(set(rows) - set(files)):
        problems.append(f"`{module}` has a catalog row but no module file under AutoproverCorpus/")
    for module in sorted(set(files) - set(rows)):
        problems.append(f"`{module}` has a module file but no catalog row")
    for module in sorted(set(rows) - set(imports)):
        problems.append(f"`{module}` has a catalog row but is not imported by AutoproverCorpus.lean")
    for module in sorted(set(imports) - set(rows)):
        problems.append(f"`{module}` is imported by AutoproverCorpus.lean but has no catalog row")
    for module in sorted(set(files) - set(imports)):
        problems.append(f"`{module}` has a module file but is not imported by AutoproverCorpus.lean — it is never built")
    for module in sorted(set(imports) - set(files)):
        problems.append(f"`{module}` is imported by AutoproverCorpus.lean but has no module file")

    for module in sorted(set(rows) & set(files) & set(imports)):
        areas = {"catalog": rows[module], "import": imports[module], "file path": files[module]}
        if len(set(areas.values())) != 1:
            detail = ", ".join(f"{where} says {area}" for where, area in areas.items())
            problems.append(f"`{module}` is filed under different areas: {detail}")

    return problems


def check_counts(catalog: Catalog) -> list[str]:
    """Check 2: every count the catalog states matches the rows it carries."""
    problems: list[str] = []

    actual: dict[str, int] = {}
    for row in catalog.rows:
        actual[row.area] = actual.get(row.area, 0) + 1

    for area in catalog.area_order:
        if area not in catalog.footers:
            problems.append(f"area `{area}` has no `{area}: N modules.` footer line")
            continue
        stated, lineno = catalog.footers[area]
        if stated != actual.get(area, 0):
            problems.append(
                f"CATALOG.md:{lineno}: `{area}` footer says {stated} modules, the table has {actual.get(area, 0)}"
            )
    for area in sorted(set(catalog.footers) - set(catalog.area_order)):
        problems.append(f"a `{area}: N modules.` footer names an area with no `## {area}` table")

    if catalog.total_line is None:
        problems.append("CATALOG.md has no Total line")
        return problems

    total = _TOTAL.match(catalog.total_line)
    if not total:
        problems.append(f"CATALOG.md:{catalog.total_lineno}: Total line does not have the expected shape: {catalog.total_line}")
        return problems

    where = f"CATALOG.md:{catalog.total_lineno}"
    if int(total.group("areas")) != len(catalog.area_order):
        problems.append(f"{where}: Total says {total.group('areas')} areas, the catalog has {len(catalog.area_order)}")
    if int(total.group("modules")) != len(catalog.rows):
        problems.append(f"{where}: Total says {total.group('modules')} modules, the catalog has {len(catalog.rows)} rows")

    stated_breakdown: dict[str, int] = {}
    for entry in total.group("breakdown").split(","):
        entry = entry.strip()
        if not entry:
            continue
        parsed = _BREAKDOWN_ENTRY.match(entry)
        if not parsed:
            problems.append(f"{where}: Total breakdown entry `{entry}` is not `<Area> <count>`")
            continue
        stated_breakdown[parsed.group("area")] = int(parsed.group("count"))
    for area in catalog.area_order:
        if area not in stated_breakdown:
            problems.append(f"{where}: Total breakdown omits `{area}`")
        elif stated_breakdown[area] != actual.get(area, 0):
            problems.append(
                f"{where}: Total breakdown says {area} {stated_breakdown[area]}, the table has {actual.get(area, 0)}"
            )
    for area in sorted(set(stated_breakdown) - set(catalog.area_order)):
        problems.append(f"{where}: Total breakdown names `{area}`, which is not an area of the catalog")

    full = sum(1 for row in catalog.rows if row.flag == "full")
    scoped = sum(1 for row in catalog.rows if _SCOPED.match(row.flag))
    if int(total.group("full")) != full:
        problems.append(f"{where}: Total says {total.group('full')} flagged `full`, the tables have {full}")
    if int(total.group("scoped")) != scoped:
        problems.append(f"{where}: Total says {total.group('scoped')} flagged `scoped`, the tables have {scoped}")

    return problems


def check_scope_flags(catalog: Catalog) -> list[str]:
    """Check 3: every flag is `full`, or `scoped` with a restriction stated."""
    problems: list[str] = []
    for row in catalog.rows:
        if row.flag == "full":
            continue
        scoped = _SCOPED.match(row.flag)
        if scoped:
            if not scoped.group("restriction").strip():
                problems.append(f"CATALOG.md:{row.lineno}: `{row.module}` is flagged scoped with no restriction stated")
            continue
        if row.flag.strip().lower().startswith("scoped"):
            problems.append(f"CATALOG.md:{row.lineno}: `{row.module}` is flagged scoped with no restriction stated")
        else:
            problems.append(f"CATALOG.md:{row.lineno}: `{row.module}` has scope flag `{row.flag}`, expected `full` or `scoped — <restriction>`")
    return problems


CHECK_SETS = "catalog rows == imports == module files"
CHECK_COUNTS = "stated counts match the rows"
CHECK_FLAGS = "every scoped row states its restriction"


def run_checks(corpus_dir: Path) -> list[tuple[str, list[str]]]:
    """Run all three checks over a corpus directory; return per-check problems."""
    catalog = parse_catalog(corpus_dir / "CATALOG.md")
    imports, import_problems = parse_imports(corpus_dir / "AutoproverCorpus.lean")
    files, file_problems = scan_files(corpus_dir / "AutoproverCorpus")

    return [
        (
            CHECK_SETS,
            catalog.malformed
            + import_problems
            + file_problems
            + check_sets(catalog, imports, files),
        ),
        (CHECK_COUNTS, check_counts(catalog)),
        (CHECK_FLAGS, check_scope_flags(catalog)),
    ]


def _first_row(catalog_text: str) -> tuple[str, str]:
    """Return (area, module) of the first catalog row, to plant violations on."""
    area = ""
    for line in catalog_text.splitlines():
        heading = _AREA_HEADING.match(line)
        if heading and heading.group("area") not in _NON_AREA_HEADINGS:
            area = heading.group("area")
        if line.startswith("| ") and line != _TABLE_HEADER and line.replace(" ", "") != _TABLE_RULE:
            return area, line.strip().strip("|").split("|")[0].strip()
    raise SystemExit("selftest: CATALOG.md has no table rows to mutate")


def selftest(source_dir: Path) -> int:
    """Plant one violation at a time in a copy and require the check to fail."""
    catalog_text = (source_dir / "CATALOG.md").read_text(encoding="utf-8")
    area, module = _first_row(catalog_text)

    def drop_catalog_row(d: Path) -> None:
        path = d / "CATALOG.md"
        kept = [ln for ln in path.read_text(encoding="utf-8").splitlines() if not ln.startswith(f"| {module} |")]
        path.write_text("\n".join(kept) + "\n", encoding="utf-8")

    def drop_import(d: Path) -> None:
        path = d / "AutoproverCorpus.lean"
        kept = [ln for ln in path.read_text(encoding="utf-8").splitlines() if ln.strip() != f"import AutoproverCorpus.{area}.{module}"]
        path.write_text("\n".join(kept) + "\n", encoding="utf-8")

    def add_stray_module(d: Path) -> None:
        (d / "AutoproverCorpus" / area / "SelftestGhostModule.lean").write_text("/- planted -/\n", encoding="utf-8")

    def delete_module_file(d: Path) -> None:
        (d / "AutoproverCorpus" / area / f"{module}.lean").unlink()

    def bump_area_footer(d: Path) -> None:
        path = d / "CATALOG.md"
        text = path.read_text(encoding="utf-8")
        for count in range(100):
            marker = f"\n{area}: {count} modules.\n"
            if marker in text:
                path.write_text(text.replace(marker, f"\n{area}: {count + 1} modules.\n"), encoding="utf-8")
                return
        raise SystemExit(f"selftest: no `{area}: N modules.` footer to mutate")

    def corrupt_total(d: Path) -> None:
        path = d / "CATALOG.md"
        text = path.read_text(encoding="utf-8")
        match = re.search(r"(\d+) flagged `full`", text)
        if not match:
            raise SystemExit("selftest: no Total line to mutate")
        path.write_text(
            text.replace(match.group(0), f"{int(match.group(1)) + 7} flagged `full`", 1),
            encoding="utf-8",
        )

    def blank_a_restriction(d: Path) -> None:
        path = d / "CATALOG.md"
        lines = path.read_text(encoding="utf-8").splitlines()
        for i, line in enumerate(lines):
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if line.startswith("| ") and len(cells) == 4 and _SCOPED.match(cells[3]):
                cells[3] = "scoped"
                lines[i] = "| " + " | ".join(cells) + " |"
                path.write_text("\n".join(lines) + "\n", encoding="utf-8")
                return
        raise SystemExit("selftest: no scoped row to mutate")

    planted = [
        (f"catalog row for `{module}` deleted", drop_catalog_row, CHECK_SETS),
        (f"import of `{module}` deleted", drop_import, CHECK_SETS),
        ("a module file with no catalog row and no import", add_stray_module, CHECK_SETS),
        (f"module file for `{module}` deleted, row and import left behind", delete_module_file, CHECK_SETS),
        (f"`{area}` per-area footer count off by one", bump_area_footer, CHECK_COUNTS),
        ("Total `full` count off by seven", corrupt_total, CHECK_COUNTS),
        ("a scoped row with its restriction removed", blank_a_restriction, CHECK_FLAGS),
    ]

    undetected: list[str] = []
    with tempfile.TemporaryDirectory() as tmp:
        for index, (description, mutate, expected) in enumerate(planted):
            work = Path(tmp) / f"planted{index}"
            work.mkdir()
            shutil.copy2(source_dir / "CATALOG.md", work / "CATALOG.md")
            shutil.copy2(source_dir / "AutoproverCorpus.lean", work / "AutoproverCorpus.lean")
            shutil.copytree(source_dir / "AutoproverCorpus", work / "AutoproverCorpus")
            mutate(work)

            problems = dict(run_checks(work))
            if problems.get(expected):
                print(f"CAUGHT ({expected}): {description}")
            else:
                undetected.append(f"{description} — `{expected}` did not fail")
                print(f"MISSED ({expected}): {description}")

    if undetected:
        print(f"\ncheck_catalog.py --selftest: {len(undetected)} planted violation(s) went undetected", file=sys.stderr)
        return 1
    print(f"\ncheck_catalog.py --selftest: all {len(planted)} planted violations were caught")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Check corpus/CATALOG.md against the corpus.")
    parser.add_argument(
        "--corpus-dir",
        type=Path,
        default=Path(__file__).resolve().parent,
        help="the corpus/ directory to check (default: the one holding this script)",
    )
    parser.add_argument(
        "--selftest",
        action="store_true",
        help="plant violations in a temporary copy and require each to be caught",
    )
    args = parser.parse_args(argv)

    corpus_dir: Path = args.corpus_dir.resolve()
    catalog_path = corpus_dir / "CATALOG.md"
    import_path = corpus_dir / "AutoproverCorpus.lean"
    module_root = corpus_dir / "AutoproverCorpus"

    for path in (catalog_path, import_path, module_root):
        if not path.exists():
            print(f"FAIL: {path} does not exist", file=sys.stderr)
            return 1

    if args.selftest:
        return selftest(corpus_dir)

    checks = run_checks(corpus_dir)

    failed = 0
    for name, problems in checks:
        if problems:
            failed += 1
            print(f"FAIL: {name}")
            for problem in problems:
                print(f"  - {problem}")
        else:
            print(f"PASS: {name}")

    if failed:
        print(f"\ncheck_catalog.py: {failed} of {len(checks)} checks FAILED", file=sys.stderr)
        return 1
    rows = len(parse_catalog(catalog_path).rows)
    print(f"\ncheck_catalog.py: {len(checks)} checks passed; {rows} catalog rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
