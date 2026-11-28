"""Refresh LeanSolid's README and website metrics from the current library."""

import argparse
from html.parser import HTMLParser
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parent.parent
MARKDOWN = ROOT / "README.md"
WEBSITE = ROOT / "website/index.html"
LEAN_OUTPUT = re.compile(r"^.*LEANSOLID_METRICS (\d+) (\d+) (\d+)\s*$", re.MULTILINE)
SOURCE_TOKEN = re.compile(r'/-|-/|--|r#*"|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\\n])\'|\n')


def count_lean_lines(source: str) -> int:
    """Count physical lines containing Lean code, preserving quoted literals."""
    lines = depth = cursor = 0
    has_code = False
    while cursor < len(source):
        match = SOURCE_TOKEN.search(source, cursor)
        if match is None:
            return lines + int(has_code or (depth == 0 and bool(source[cursor:].strip())))
        if depth == 0 and source[cursor:match.start()].strip():
            has_code = True
        token = match[0]
        cursor = match.end()
        if token == "\n":
            lines += has_code
            has_code = False
        elif token == "/-":
            depth += 1
        elif token == "-/" and depth:
            depth -= 1
        elif depth:
            # Inside a block comment, quotes and line-comment markers carry no meaning.
            cursor = match.start() + 1
        elif token == "--":
            newline = source.find("\n", cursor)
            cursor = len(source) if newline == -1 else newline
        elif token.startswith('r') and token.endswith('"'):
            close = '"' + token[1:-1]
            end = source.find(close, cursor)
            if end == -1:
                raise ValueError("Unterminated Lean raw string")
            lines += source.count("\n", cursor, end)
            cursor = end + len(close)
            has_code = True
        else:
            lines += token.count("\n")
            has_code = True
    return lines + has_code


class RegistryRows(HTMLParser):
    def __init__(self):
        super().__init__()
        self.in_registry = False
        self.rows = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == "table":
            self.in_registry = attrs.get("aria-labelledby") == "problems"
        elif self.in_registry and tag == "th" and attrs.get("scope") == "row":
            self.rows += 1

    def handle_endtag(self, tag):
        if tag == "table":
            self.in_registry = False


def collect_metrics() -> dict[str, str]:
    result = subprocess.run(
        ["lake", "lean", "scripts/ProjectMetrics.lean"], cwd=ROOT,
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    output = result.stdout + result.stderr
    match = LEAN_OUTPUT.search(output)
    if result.returncode or not match:
        raise SystemExit(f"Lean metrics collection failed.\n{output}")
    declarations, verified, total = map(int, match.groups())
    if not 0 < verified <= total <= declarations:
        raise SystemExit(f"Unexpected Lean metrics: {match.groups()}")
    library_files = [ROOT / "LeanSolid.lean", *(ROOT / "LeanSolid").rglob("*.lean")]
    lines = sum(count_lean_lines(file.read_text(encoding="utf-8-sig")) for file in library_files)

    index = (ROOT / "LandmarkResults/README.md").read_text(encoding="utf-8")
    entries = re.findall(r"^\| \[[^\]]+\]\(([^)]+/README\.md)\)", index, re.MULTILINE)
    coverage = []
    for entry in dict.fromkeys(entries):
        path = ROOT / "LandmarkResults" / entry
        markers = re.findall(r"<!-- metrics-paper: (complete|partial) -->", path.read_text(encoding="utf-8"))
        if len(markers) != 1:
            raise SystemExit(f"Expected one metrics-paper coverage marker in {path}")
        coverage.append(markers[0])
    registry = RegistryRows()
    registry.feed((ROOT / "website/OpenProblems/index.html").read_text(encoding="utf-8"))
    return {
        "declarations": f"{declarations:,}",
        "verified": f"{verified:,} / {total:,}",
        "papers": f"{coverage.count('complete')} complete · {coverage.count('partial')} partial",
        "landmarks": f"{len(coverage):,}",
        "lines": f"{lines:,}",
        "problems": f"{registry.rows:,}",
    }


def update(path: Path, values: dict[str, str], check: bool) -> bool:
    original = path.read_text(encoding="utf-8")
    updated = original
    for key, value in values.items():
        pattern = rf"(<!-- metric:{key} -->).*?(<!-- /metric:{key} -->)"
        updated, matches = re.subn(pattern, lambda m: f"{m[1]}{value}{m[2]}", updated)
        if matches != 1:
            raise SystemExit(f"Expected one {key} cell in {path}")
    if original == updated:
        return True
    if check:
        print(f"Out of date: {path.relative_to(ROOT)}")
        return False
    path.write_text(updated, encoding="utf-8", newline="\n")
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Report stale tables without editing them")
    args = parser.parse_args()
    values = collect_metrics()
    results = [update(path, values, args.check) for path in (MARKDOWN, WEBSITE)]
    for key, value in values.items():
        print(f"{key}: {value}")
    return 0 if all(results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
