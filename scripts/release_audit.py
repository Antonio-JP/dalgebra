#!/usr/bin/env python3
import argparse
import ast
import re
import subprocess
from pathlib import Path

RE_HUNK = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")


def run(cmd):
    r'''Run a commend as a subpocress and reads its output'''
    return subprocess.check_output(cmd, text=True).strip()


def try_run(cmd):
    r'''Run a command as a subprocess and filters its Exception (in case an error occurs)'''
    try:
        return run(cmd)
    except subprocess.CalledProcessError:
        return ""


def latest_tag():
    r'''Get the latest tag in the git repository'''
    return try_run(["git", "describe", "--tags", "--abbrev=0"])


def changed_python_files(base, head):
    r'''Get a list of changed python files between two git revisions'''
    out = try_run(["git", "diff", "--name-only", f"{base}..{head}", "--", "dalgebra"])
    if not out:
        return []
    return [Path(line) for line in out.splitlines() if line.endswith(".py") and Path(line).exists()]

def added_line_numbers(base, head, file_path):
    r'''Get the line numbers of added lines in a file between two git revisions'''
    out = try_run(["git", "diff", "-U0", f"{base}..{head}", "--", str(file_path)])
    added = set()
    new_line = 0
    in_hunk = False

    for line in out.splitlines():
        hunk = RE_HUNK.match(line)
        if hunk:
            new_line = int(hunk.group(1))
            in_hunk = True
            continue

        if not in_hunk:
            continue

        if line.startswith("+") and not line.startswith("+++"):
            added.add(new_line)
            new_line += 1
        elif line.startswith("-") and not line.startswith("---"):
            continue
        elif line.startswith(" "):
            new_line += 1

    return added


def is_magic_name(name):
    r'''Check if a name is a magic method (starts and ends with double underscores)'''
    return name.startswith("__") and name.endswith("__")

def is_private_name(name):
    r'''Check if a name is a private method (starts with a single underscore but doesn't end with an underscore)'''
    return name.startswith("_") and not name.startswith("__") and not name.endswith("__")

def iter_symbols(tree):
    r'''Method to iterate over all the elements on a tree. It uses an inner Visitor class with the functionality when visiting the nodes.'''
    items = []

    class Visitor(ast.NodeVisitor):
        def __init__(self):
            self.stack = []

        def visit_ClassDef(self, node):
            qname = ".".join([name for _, name in (self.stack + [("class", node.name)])])
            doc = ast.get_docstring(node) or ""
            nested_in_class = any(kind == "class" for kind, _ in self.stack)
            items.append(
                {
                    "lineno": node.lineno,
                    "kind": "class",
                    "name": node.name,
                    "qname": qname,
                    "docstring": bool(doc.strip()),
                    "doctest": ("sage:" in doc) or (">>>" in doc) or ("::NO EXAMPLE::" in doc),
                    "nested_warning": nested_in_class,
                    "magic_warning": False,
                    "private_warning": False,
                    "decorated_warning": bool(node.decorator_list),
                    "skip": False,
                }
            )
            self.stack.append(("class", node.name))
            self.generic_visit(node)
            self.stack.pop()

        def visit_FunctionDef(self, node):
            qname = ".".join([name for _, name in (self.stack + [("func", node.name)])])
            doc = ast.get_docstring(node) or ""
            nested_in_function = any(kind == "func" for kind, _ in self.stack)
            is_init_method = node.name == "__init__" and any(kind == "class" for kind, _ in self.stack)
            is_magic = is_magic_name(node.name) and node.name != "__init__"
            is_private = is_private_name(node.name)
            items.append(
                {
                    "lineno": node.lineno,
                    "kind": "func",
                    "name": node.name,
                    "qname": qname,
                    "docstring": bool(doc.strip()),
                    "doctest": ("sage:" in doc) or (">>>" in doc),
                    "nested_warning": nested_in_function,
                    "magic_warning": is_magic,
                    "private_warning": (not is_magic) and is_private,
                    "decorated_warning": bool(node.decorator_list),
                    "skip": is_init_method,
                }
            )
            self.stack.append(("func", node.name))
            self.generic_visit(node)
            self.stack.pop()

        def visit_AsyncFunctionDef(self, node):
            self.visit_FunctionDef(node)

    Visitor().visit(tree)
    return items


def find_def_records(file_path):
    r''''''
    text = file_path.read_text(encoding="utf-8")
    if "::IGNORE AUDIT::" in text:
        return []
    tree = ast.parse(text)
    return iter_symbols(tree)


def main():
    parser = argparse.ArgumentParser(
        description="Audit new classes/functions/methods since a reference for docstring/doctest coverage."
    )
    parser.add_argument("--base", default=None, help="Base revision/tag (default: latest tag)")
    parser.add_argument("--head", default="HEAD", help="Head revision (default: HEAD)")
    parser.add_argument(
        "--no-ok",
        action="store_true",
        help="Skip all symbols that are OK.",
    )
    parser.add_argument(
        "--ignore-decorated",
        action="store_true",
        help="Skip decorated symbols from the audit output.",
    )
    parser.add_argument(
        "--ignore-magic",
        action="store_true",
        help="Skip magic methods (__***__) from the audit output.",
    )
    parser.add_argument(
        "--ignore-private",
        action="store_true",
        help="Skip private methods (__***) from the audit output.",
    )
    parser.add_argument(
        "--warnings-as-ok",
        action="store_true",
        help="Return exit code 0 when there are only WARNING entries.",
    )
    args = parser.parse_args()

    base = args.base or latest_tag()
    if not base:
        print("No tags found. Provide --base <revision> to compare against.")
        return 1
    elif base == "origin":
        base = "8f15ae11bf1caac8e56aab49537ef3e9502bd3da"

    files = changed_python_files(base, args.head)
    if not files:
        print(f"No changed Python files in dalgebra between {base}..{args.head}.")
        return 0

    rows = []
    for file_path in files:
        added_lines = added_line_numbers(base, args.head, file_path)
        if not added_lines:
            continue

        try:
            definitions = find_def_records(file_path)
        except SyntaxError:
            continue

        for symbol in definitions:
            if symbol["skip"]:
                continue
            if args.ignore_decorated and symbol["decorated_warning"]:
                continue
            if args.ignore_magic and symbol["magic_warning"]:
                continue
            if args.ignore_private and symbol["private_warning"]:
                continue
            if symbol["lineno"] in added_lines:
                warning_reasons = []
                if symbol["nested_warning"]:
                    warning_reasons.append("nested")
                if symbol["magic_warning"]:
                    warning_reasons.append("magic")
                if symbol["private_warning"]:
                    warning_reasons.append("private")
                if symbol["decorated_warning"]:
                    warning_reasons.append("decorated")
                if not symbol["doctest"]:
                    warning_reasons.append("doctest")

                missing_fields = []
                if not symbol["docstring"]:
                    missing_fields.append("docstring")

                ## Computing the severity:
                ## - If docstring is missing but it is magic or nested, we issue a warning, otherwise an error
                ## - If doctest is missing, we issue a warning.
                severity = "ERROR" if (missing_fields and all(el not in warning_reasons for el in ("magic", "nested", "private"))) else "WARNING" if warning_reasons else "OK"

                if args.no_ok and (severity == "OK" or (severity == "WARNING" and args.warnings_as_ok)):
                    continue

                rows.append(
                    {
                        "file": str(file_path) + f":{symbol["lineno"]}",
                        "kind": symbol["kind"],
                        "symbol": symbol["qname"],
                        "docstring": symbol["docstring"],
                        "doctest": symbol["doctest"],
                        "missing": ",".join(missing_fields) if missing_fields else "-",
                        "tag": severity,
                        "warning_reasons": ",".join(warning_reasons) if warning_reasons else "-",
                    }
                )

    print(f"Release audit for range: {base}..{args.head}")
    if not rows:
        print(f"No newly added class/function/method definitions detected in that range{' with errors or warnings' if args.no_ok else ''}.")
        return 0

    size_file = max(len(row["file"]) for row in rows)
    size_symbol = max(len(row["symbol"]) for row in rows) 

    print("\nSymbol checks:")
    print("- docstring: symbol has inline docstring")
    print("- doctest: docstring contains a doctest marker ('sage:' or '>>>')")
    print("- tag: missing coverage severity (ERROR or WARNING)")
    print("- warning_reasons: nested, magic, and/or decorated")
    print(
        "\n{:<{size_file}} {:<7} {:<{size_symbol}} {:<9} {:<18} {:<25}".format(
            "file", "kind", "symbol", "tag", "missing", "warning_reasons",
            size_file=size_file+3, size_symbol=size_symbol+3
        )
    )
    print("-" * ((size_file+3)+7+(size_symbol+3)+9+18+25))

    missing_errors = []
    missing_warnings = []
    for row in rows:
        print(
            "{:<{size_file}} {:<7} {:<{size_symbol}} {:<9} {:<18} {:<25}".format(
                row["file"][:size_file],
                row["kind"][:7],
                row["symbol"][:size_symbol],
                row["tag"],
                row["missing"][:18],
                row["warning_reasons"][:25],
                size_file=size_file+3, size_symbol=size_symbol+3
            )
        )
        if row["tag"] == "ERROR":
            missing_errors.append(row)
        elif row["tag"] == "WARNING":
            missing_warnings.append(row)

    if missing_errors:
        print(
            f"\n{len(missing_errors)} ERROR symbol(s) and {len(missing_warnings)} WARNING symbol(s) need manual review."
        )
        return 2

    if missing_warnings:
        print(f"\n{len(missing_warnings)} WARNING symbol(s) need manual review.")
        if args.warnings_as_ok:
            print("Returning success because --warnings-as-ok is enabled.")
            return 0
        return 1

    print("\nAll added symbols have docstring and doctest markers.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
