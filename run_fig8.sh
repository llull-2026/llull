#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

./build.sh
BIN=build-eval/llull_eval

DATA=output/paper/data
mkdir -p "$DATA"

SEED=${SEED:-195626534}

run() {
    local out="$DATA/$1"; shift
    if [ -f "$out" ]; then
        echo "skip (exists): $out"
    else
        echo "run: $* -> $out"
        "$BIN" "$@" --quiet --csv "$out"
    fi
}

run "hephrw_wt_rand_m40_s$SEED.csv" heph --real-world --well-typed --n 500000 \
    --mode random-fresh --max-size 8 --stop-prob 0.85 --term-time 0.1 --max-inst 40 --seed "$SEED"
run hephrw_ill_shell.csv heph --real-world --ill-typed --n 500000 --strategy shell --max-inst 1

python3 experiments/plotFig8.py "hephrw_wt_rand_m40_s$SEED" hephrw_ill_shell
