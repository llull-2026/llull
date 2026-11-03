#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

./build.sh
BIN=build-eval/llull_eval

DATA=output/paper/data
mkdir -p "$DATA"

HOURS=${HOURS:-24}
MEM_MB=${MEM_MB:-26112}
NAME="heph_wt_enum_${HOURS}h"
OUT="$DATA/$NAME.csv"

if [ -f "$OUT" ]; then
    echo "skip (exists): $OUT"
else
    echo "run: heph well-typed enumeration for ${HOURS}h -> $OUT"
    "$BIN" heph --well-typed --variants --strategy triangle --max-inst 1 --term-time 0.1 \
        --n 4000000000000000000 --time "$(awk -v h="$HOURS" 'BEGIN { printf "%d", h * 3600 }')" --max-rss-mb "$MEM_MB" \
        --stop-when-all --quiet --progress-secs 60 \
        --trace "$DATA/$NAME.trace.csv" --trace-every 1000 --csv "$OUT"
fi

python3 experiments/plotFig6.py "$NAME"
