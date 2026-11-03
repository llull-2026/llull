#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

./build.sh
BIN=build-eval/llull_eval

DATA=output/paper/data
mkdir -p "$DATA"

SEED=${SEED:-195626534}
TOTAL=18
i=0

run() {
    local out="$DATA/$1"; shift
    i=$((i + 1))
    if [ -f "$out" ]; then
        echo "[$i/$TOTAL] skip (exists): $out"
    else
        echo "[$i/$TOTAL] run: $* -> $out"
        "$BIN" "$@" --quiet --progress-secs 60 --csv "$out"
    fi
}

for kind in wt ill; do
    kindflag="--well-typed"
    [ "$kind" = ill ] && kindflag="--ill-typed"
    run "comb_${kind}_enum.csv" comb "$kindflag" --variants --n 500000 \
        --strategy triangle --max-inst 1
    run "comb_${kind}_be.csv" comb "$kindflag" --variants --n 500000 \
        --strategy shell --max-size 10 --max-inst 1
    run "comb_${kind}_rand_m1_s$SEED.csv" comb "$kindflag" --variants --n 500000 \
        --mode random-fresh --max-size 8 --stop-prob 0.85 --max-inst 1 --seed "$SEED"
    run "fj_${kind}_enum.csv" fj "$kindflag" --variants --n 500000 \
        --strategy triangle --max-inst 1
    run "fj_${kind}_be.csv" fj "$kindflag" --variants --n 500000 \
        --strategy shell --max-size 8 --max-inst 1
    run "fj_${kind}_rand_m10_s$SEED.csv" fj "$kindflag" --variants --n 500000 \
        --mode random-persistent --max-size 8 --stop-prob 0.85 --max-inst 10 --seed "$SEED"
    run "heph_${kind}_enum.csv" heph "$kindflag" --variants --n 500000 \
        --strategy triangle --max-inst 1
    run "heph_${kind}_be.csv" heph "$kindflag" --variants --n 500000 \
        --strategy shell --max-size 8 --max-inst 1
    m=10
    [ "$kind" = ill ] && m=1
    run "heph_${kind}_rand_m${m}_s$SEED.csv" heph "$kindflag" --variants --n 500000 \
        --mode random-fresh --max-size 8 --stop-prob 0.85 --term-time 0.1 --max-inst "$m" --seed "$SEED"
done

echo "family data complete in $DATA"
