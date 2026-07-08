#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

./build.sh
BIN=build-eval/llull_eval

DATA=output/rq2compare/data
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

run fj_wt_be_m1.csv         fj            --well-typed --variants --n 100000 \
    --strategy shell --max-size 8 --max-inst 1
run fj_wt_be_concrete.csv   fj-concrete   --well-typed --variants --n 100000 \
    --strategy shell --max-size 8
run comb_wt_be_m1.csv       comb          --well-typed --variants --n 100000 \
    --strategy shell --max-size 10 --max-inst 1
run comb_wt_be_concrete.csv comb-concrete --well-typed --variants --n 100000 \
    --strategy shell --max-size 10

python3 experiments/compareProtoConcrete.py
