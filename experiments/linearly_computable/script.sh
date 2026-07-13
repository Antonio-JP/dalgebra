#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ne 0 ]; then
	echo "This script does not accept arguments."
	exit 1
fi

original_ref="$(git symbolic-ref -q --short HEAD || true)"
original_commit="$(git rev-parse --verify HEAD)"
common_base="$(git merge-base develop "$original_commit")"

git checkout "$common_base"
echo "[BASELINE] Running on merge-base with 'develop' (${common_base})."
sage examples.py

if [ -n "$original_ref" ]; then
	git checkout "$original_ref"
else
	git checkout "$original_commit"
fi

echo "[NEW] Running on original starting ref."
sage examples.py
