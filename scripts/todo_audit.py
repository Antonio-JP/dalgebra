#!/usr/bin/env python3
from __future__ import annotations

import ast
import argparse
import io
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


def analyze_file(root: Path, file_path: Path, branch: str) -> list[Finding]:
	r'''Inspect one Python file and report warnings and errors.'''
	findings: list[Finding] = []
	relative_path = file_path.relative_to(root)
	source = file_path.read_text(encoding="utf-8", errors="replace")
	lines = source.splitlines()
	docstring_line_numbers = docstring_lines(source)
	comment_line_map = comment_lines(source)

	for line_number in sorted(docstring_line_numbers):
		line = lines[line_number - 1]
		for match in TODO_PATTERN.finditer(line):
			label = match.group("label")
			if label is None or label.strip().lower() == "unassigned":
				findings.append(Finding("WARNING", relative_path, line_number, label is not None))
			elif label.strip() == branch:
				findings.append(Finding("ERROR", relative_path, line_number, label.strip()))

	for line_number, comments in sorted(comment_line_map.items()):
		for comment in comments:
			for match in TODO_PATTERN.finditer(comment):
				label = match.group("label")
				if label is None or label.strip().lower() == "unassigned":
					findings.append(Finding("WARNING", relative_path, line_number, not label is None))
				elif label.strip() == branch:
					findings.append(Finding("ERROR", relative_path, line_number, label.strip()))

	return findings


def audit_todos(root: Path, branch: str) -> list[Finding]:
	r'''Inspect all audited files and collect findings.'''
	findings: list[Finding] = []
	for file_path in python_files(root):
		findings.extend(analyze_file(root, file_path, branch))
	return findings


def print_findings(findings: list[Finding], branch: str) -> None:
	r'''Print findings in a terminal-friendly format.'''
	if not findings:
		print(f"No TODO warnings or errors found for branch '{branch}'.")
		return

	for finding in findings:
		if finding.severity == "WARNING":
			print(f"WARNING {finding.path}:{finding.line_number} {'unassigned' if finding.label is True else f'unlabelled'} TODO")
		else:
			print(
				f"ERROR {finding.path}:{finding.line_number} "
				f"TODO label '{finding.label}' matches current branch '{branch}'"
			)

	error_count = sum(finding.severity == "ERROR" for finding in findings)
	warning_count = sum(finding.severity == "WARNING" for finding in findings)
	print(f"Found {error_count} errors and {warning_count} warnings.")


def main() -> int:
	parser = argparse.ArgumentParser(
		description="Audit TODO labels in Python files against the current Git branch."
	)
	parser.parse_args()

	root = repository_root()
	try:
		branch = current_branch(root)
	except subprocess.CalledProcessError:
		print("Unable to determine the current Git branch.")
		return 2

	findings = audit_todos(root, branch)
	print_findings(findings, branch)
	return 1 if any(finding.severity == "ERROR" for finding in findings) else 0


if __name__ == "__main__":
	raise SystemExit(main())
