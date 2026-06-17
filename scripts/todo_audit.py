#!/usr/bin/env python3
from __future__ import annotations

import ast
import argparse
import io
import json
import re
import subprocess
import tokenize
from dataclasses import dataclass
from pathlib import Path

TARGET_FOLDERS = ("dalgebra", "experiments", "notebooks", "scripts")
TODO_PATTERN = re.compile(r"TODO(?:\s*\((?P<label>[^)]+)\))?")


@dataclass(frozen=True)
class Finding:
    r'''Container for audit findings.'''

    severity: str
    path: Path
    line_number: int
    label: str | None
    context: str | None = None


def run(cmd: list[str]) -> str:
    r'''Run a command as a subprocess and return its standard output.'''
    return subprocess.check_output(cmd, text=True).strip()


def repository_root() -> Path:
    r'''Return the root folder for the repository.'''
    return Path(__file__).resolve().parents[1]


def current_branch(root: Path) -> str:
    r'''Return the active Git branch for the repository.'''
    return run(["git", "-C", str(root), "rev-parse", "--abbrev-ref", "HEAD"])


def is_hidden_path(path: Path) -> bool:
    r'''Check whether a path contains a hidden file or folder.'''
    return any(part.startswith(".") for part in path.parts)


def python_files(root: Path) -> list[Path]:
    r'''Collect all Python files in the folders under audit.'''
    return sorted(
        file_path
        for folder_name in TARGET_FOLDERS
        for file_path in (root / folder_name).rglob("*.py")
        if file_path.is_file() and not is_hidden_path(file_path.relative_to(root))
    )


def notebook_files(root: Path) -> list[Path]:
    r'''Collect all notebook files in the folders under audit.'''
    return sorted(
        file_path
        for folder_name in TARGET_FOLDERS
        for file_path in (root / folder_name).rglob("*.ipynb")
        if file_path.is_file() and not is_hidden_path(file_path.relative_to(root))
    )


def classify_todo(path: Path, line_number: int, branch: str, label: str | None, context: str | None = None) -> Finding | None:
    r'''Classify one task marker according to its label and the current branch.'''
    if label is None:
        return Finding("WARNING", path, line_number, None, context)

    normalized_label = label.strip()
    if normalized_label.lower() == "unassigned":
        return Finding("WARNING", path, line_number, "unassigned", context)
    if normalized_label == branch:
        return Finding("ERROR", path, line_number, normalized_label, context)
    return None


def docstring_lines(source: str) -> set[int]:
    r'''Return the line numbers occupied by docstrings in a module.'''
    try:
        tree = ast.parse(source)
    except SyntaxError:
        return set()

    lines: set[int] = set()

    def register(body: list[ast.stmt]) -> None:
        if not body or not isinstance(body[0], ast.Expr):
            return

        value = body[0].value
        if isinstance(value, ast.Constant) and isinstance(value.value, str):
            start = body[0].lineno
            end = getattr(body[0], "end_lineno", start)
            lines.update(range(start, end + 1))

    register(tree.body)
    for node in ast.walk(tree):
        if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef)):
            register(node.body)

    return lines


def comment_lines(source: str) -> dict[int, list[str]]:
    r'''Return comment tokens grouped by line number.'''
    comments: dict[int, list[str]] = {}
    try:
        for token in tokenize.generate_tokens(io.StringIO(source).readline):
            if token.type == tokenize.COMMENT:
                comments.setdefault(token.start[0], []).append(token.string)
    except tokenize.TokenError:
        return comments

    return comments


def analyze_python_source(relative_path: Path, source: str, branch: str, context: str | None = None) -> list[Finding]:
    r'''Inspect Python source text and report warnings and errors.'''
    findings: list[Finding] = []
    lines = source.splitlines()
    docstring_line_numbers = docstring_lines(source)
    comment_line_map = comment_lines(source)

    for line_number in sorted(docstring_line_numbers):
        line = lines[line_number - 1]
        for match in TODO_PATTERN.finditer(line):
            finding = classify_todo(relative_path, line_number, branch, match.group("label"), context)
            if finding is not None:
                findings.append(finding)

    for line_number, comments in sorted(comment_line_map.items()):
        for comment in comments:
            for match in TODO_PATTERN.finditer(comment):
                finding = classify_todo(relative_path, line_number, branch, match.group("label"), context)
                if finding is not None:
                    findings.append(finding)

    return findings


def analyze_file(root: Path, file_path: Path, branch: str) -> list[Finding]:
    r'''Inspect one Python file and report warnings and errors.'''
    relative_path = file_path.relative_to(root)
    source = file_path.read_text(encoding="utf-8", errors="replace")
    return analyze_python_source(relative_path, source, branch)


def analyze_notebook_file(root: Path, file_path: Path, branch: str) -> list[Finding]:
    r'''Inspect one notebook file and report findings from cell source.'''
    relative_path = file_path.relative_to(root)
    try:
        notebook = json.loads(file_path.read_text(encoding="utf-8", errors="replace"))
    except json.JSONDecodeError:
        return []

    findings: list[Finding] = []
    for cell_number, cell in enumerate(notebook.get("cells", []), start=1):
        source = cell.get("source", [])
        if isinstance(source, list):
            source_text = "".join(source)
        elif isinstance(source, str):
            source_text = source
        else:
            continue

        if not source_text:
            continue

        context = f"cell {cell_number}"
        if cell.get("cell_type") == "code":
            findings.extend(analyze_python_source(relative_path, source_text, branch, context))
            continue

        for line_number, line in enumerate(source_text.splitlines(), start=1):
            for match in TODO_PATTERN.finditer(line):
                finding = classify_todo(relative_path, line_number, branch, match.group("label"), context)
                if finding is not None:
                    findings.append(finding)

    return findings


def audit_todos(root: Path, branch: str) -> list[Finding]:
    r'''Inspect all audited files and collect findings.'''
    findings: list[Finding] = []
    for file_path in python_files(root):
        findings.extend(analyze_file(root, file_path, branch))
    for file_path in notebook_files(root):
        findings.extend(analyze_notebook_file(root, file_path, branch))
    return findings


def print_findings(findings: list[Finding], branch: str, warnings: bool) -> None:
    r'''Print findings in a terminal-friendly format.'''
    if not findings:
        print(f"No TODO warnings or errors found for branch '{branch}'.")
        return

    for finding in findings:
        location = f"{finding.path}:{finding.line_number}"
        if finding.context is not None:
            location = f"{location} ({finding.context})"
        if finding.severity == "WARNING" and warnings:
            print(f"WARNING {location} {'unassigned' if finding.label == 'unassigned' else 'unlabelled'} TODO")
        elif finding.severity == "ERROR":
            print(
                f"ERROR {location} "
                f"TODO label '{finding.label}' matches current branch '{branch}'"
            )

    error_count = sum(finding.severity == "ERROR" for finding in findings)
    warning_count = sum(finding.severity == "WARNING" for finding in findings)
    print(f"Found {error_count} errors and {warning_count} warnings.")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Audit TODO labels in Python files and notebooks against the current Git branch."
    )
    parser.add_argument(
        "--warnings",
        action="store_true",
        help="List also the warnings.",
    )
    args = parser.parse_args()

    root = repository_root()
    try:
        branch = current_branch(root)
    except subprocess.CalledProcessError:
        print("Unable to determine the current Git branch.")
        return 2

    findings = audit_todos(root, branch)
    print_findings(findings, branch, warnings=args.warnings)
    
    return 1 if any(finding.severity == "ERROR" for finding in findings) else 0


if __name__ == "__main__":
    raise SystemExit(main())
