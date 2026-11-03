#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

./build.sh
BIN=build-eval/llull_eval

DATA=output/paper/data
mkdir -p "$DATA"

run() {
    local out="$DATA/$1"; shift
    if [ -f "$out" ]; then
        echo "skip (exists): $out"
    else
        echo "run: $* -> $out"
        "$BIN" "$@" --quiet --csv "$out"
    fi
}

run comb_wt_be.csv comb --well-typed --variants --n 500000 \
    --strategy shell --max-size 10 --max-inst 1
run fj_wt_be.csv   fj   --well-typed --variants --n 500000 \
    --strategy shell --max-size 8 --max-inst 1

python3 experiments/plotFig3to5.py prototerm
