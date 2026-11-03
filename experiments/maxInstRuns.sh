#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

ulimit -v $((12 * 1024 * 1024))
ulimit -s $((1024 * 1024)) 2>/dev/null || true

./build.sh
BIN=build-eval/llull_eval

DATA=output/charts/maxinst
mkdir -p "$DATA"

SEED=${SEED:-195626534}
TOTAL=54
i=0

run() {
    local out="$DATA/$1"; shift
    i=$((i + 1))
    if [ -f "$out" ]; then
        echo "[$i/$TOTAL] skip (exists): $out"
    else
        echo "[$i/$TOTAL] run: $* -> $out"
        "$BIN" "$@" --quiet --progress-secs 30 --csv "$out"
    fi
}

for kind in wt ill; do
    kindflag="--well-typed"
    [ "$kind" = ill ] && kindflag="--ill-typed"
    for m in 1 10 100; do
        run "comb_${kind}_enum_m${m}.csv" comb "$kindflag" --variants --n 100000 \
            --strategy triangle --max-inst "$m"
        run "comb_${kind}_be_m${m}.csv"   comb "$kindflag" --variants --n 100000 \
            --strategy shell --max-size 10 --max-inst "$m"
        run "comb_${kind}_rand_m${m}.csv" comb "$kindflag" --variants --n 100000 \
            --mode random-fresh --max-size 8 --stop-prob 0.85 --max-inst "$m" --seed "$SEED"
        run "fj_${kind}_enum_m${m}.csv"   fj   "$kindflag" --variants --n 100000 \
            --strategy triangle --max-inst "$m"
        run "fj_${kind}_be_m${m}.csv"     fj   "$kindflag" --variants --n 100000 \
            --strategy shell --max-size 8 --max-inst "$m"
        run "fj_${kind}_rand_m${m}.csv"   fj   "$kindflag" --variants --n 100000 \
            --mode random-persistent --max-size 8 --stop-prob 0.85 --max-inst "$m" --seed "$SEED"
        run "heph_${kind}_enum_m${m}.csv" heph "$kindflag" --variants --n 100000 \
            --strategy triangle --max-inst "$m"
        run "heph_${kind}_be_m${m}.csv"   heph "$kindflag" --variants --n 100000 \
            --strategy shell --max-size 8 --max-inst "$m"
        run "heph_${kind}_rand_m${m}.csv" heph "$kindflag" --variants --n 100000 \
            --mode random-fresh --max-size 8 --stop-prob 0.85 --term-time 0.1 --max-inst "$m" \
            --seed "$SEED"
    done
done

echo "max_inst data complete in $DATA"
