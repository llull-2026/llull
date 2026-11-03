#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

./build.sh
BIN=build-eval/llull_eval

export DATA=output/charts/data
mkdir -p "$DATA"
TSV=charts/runs.tsv
OOM_MB=${OOM_MB:-24576}

row() { awk -F'\t' -v n="$1" '$1 == n' "$TSV"; }

run_eval() {
    local name=$1 fmt=$2; shift 2
    local out="$DATA/$name.csv"
    if [ -f "$out" ]; then
        echo "skip (exists): $out"
        return
    fi
    echo "run: $* -> $out"
    if [ "$fmt" = oom ]; then
        local limit=()
        [ -n "$OOM_HOURS" ] && limit=(--time "$(awk -v h="$OOM_HOURS" 'BEGIN { printf "%d", h * 3600 }')")
        "$BIN" "$@" --n 4000000000000000000 "${limit[@]}" --max-rss-mb "$OOM_MB" --quiet \
            --progress-secs 60 --trace "$DATA/$name.trace.csv" --trace-every 1000 --csv "$out"
    else
        "$BIN" "$@" --n 100000 --quiet --csv "$out"
    fi
}

one() {
    local line name fmt args
    line=$(row "$1")
    [ -n "$line" ] || { echo "no run named $1 in $TSV" >&2; exit 1; }
    IFS=$'\t' read -r name fmt args <<< "$line"
    case $fmt in
        normal|oom)
            run_eval "$name" "$fmt" $args
            python3 experiments/makeChart.py "$fmt" "$DATA/$name" -o "output/charts/$name.png"
            ;;
        breccia)
            set -- $args
            local base=$1 lang=$2; shift 2
            [ -f "$DATA/$base.csv" ] || one "$base"
            experiments/brecciaRun.sh "$name" "$lang" "$@"
            python3 experiments/makeChart.py breccia "$DATA/$base" "$DATA/$name" -o "output/charts/$name.png"
            ;;
    esac
}

if [ $# -eq 0 ]; then
    set -- $(cut -f1 "$TSV")
fi
for n in "$@"; do
    one "$n"
done
