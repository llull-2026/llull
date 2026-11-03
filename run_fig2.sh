#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

./build.sh
BIN=build-lve/lazy_vs_eager

DATA=output/paper/data
mkdir -p "$DATA"

LAZY="$DATA/fig2_comb_ill_lazy.csv"
EAGER="$DATA/fig2_comb_ill_eager.csv"
LIMIT=${LAZY_LIMIT:-7200}

if [ -f "$EAGER" ]; then
    echo "skip (exists): $EAGER"
else
    start=$(date +%s.%N)
    timeout "$LIMIT" "$BIN" comb --lazy --ill-typed --waves 3 --target 10000000 \
        --sample 0.25 --csv "$LAZY" | tee "$DATA/fig2_comb_ill_lazy.log" || true
    secs=$(sed -n 's/.* in \([0-9.]*\)s.*/\1/p' "$DATA/fig2_comb_ill_lazy.log")
    [ -n "$secs" ] || secs=$(awk -v a="$start" -v b="$(date +%s.%N)" 'BEGIN { printf "%.2f", b - a }')
    echo "lazy took ${secs}s; running eager with that timeout"
    "$BIN" comb --eager --ill-typed --timeout "$secs" --sample 0.25 --csv "$EAGER.part"
    mv "$EAGER.part" "$EAGER"
fi

python3 experiments/plotFig2.py
