#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if [ $# -lt 2 ]; then
    echo "usage: experiments/brecciaRun.sh NAME comb|fj|heph [-u] [bound=value ...]" >&2
    exit 1
fi
NAME=$1 LANG=$2; shift 2
case "$LANG" in
    comb) brc=refmut; relation=RefMutTracking; merge=(-u Term) ;;
    fj) brc=fj; relation=ExpressionWithContextTracking; merge=(-u ExpressionWithContext) ;;
    heph) brc=heph; relation=HephTracking; merge=(-u Term -u Args) ;;
    *) echo "unknown language $LANG" >&2; exit 1 ;;
esac
flags=()
for a in "$@"; do
    case $a in
        -u) flags+=("${merge[@]}") ;;
        *=*) flags+=("-${a%%=*}" "${a#*=}") ;;
        *) echo "bad argument $a" >&2; exit 1 ;;
    esac
done

[ -x build-eval/llull_eval ] || ./build.sh
DATA=${DATA:-output/charts/data}
OUT="$DATA/$NAME.csv"
WORK="$DATA/$NAME.breccia"
if [ -f "$OUT" ]; then
    echo "skip (exists): $OUT"
    exit 0
fi
mkdir -p "$WORK"

start=$(date +%s.%N)
if [ -f "breccia/$NAME/run.egg" ]; then
    cp "breccia/$NAME/run.egg" "$WORK/run.egg"
else
    (cd "$WORK" && "$ROOT/bin/breccia" "$ROOT/breccia/languages/$brc.brc" "${flags[@]}" > compile.log 2>&1)
    sed -E -e '/\(print-(function|size) /d' "$WORK/$brc.egg" > "$WORK/run.egg"
    echo "(print-function $relation 1000000000)" >> "$WORK/run.egg"
fi
echo "run: egglog $WORK/run.egg (${flags[*]})"
if ! timeout "${BRECCIA_TIMEOUT:-21600}" /usr/bin/time -f "%M %e" -o "$DATA/$NAME.mem" \
        bin/egglog "$WORK/run.egg" > "$WORK/programs.txt" 2> "$WORK/egglog.err"; then
    echo "breccia did not finish within ${BRECCIA_TIMEOUT:-21600}s" >&2
    exit 2
fi
secs=$(awk -v a="$start" -v b="$(date +%s.%N)" 'BEGIN { printf "%.1f", b - a }')
echo "breccia took ${secs}s"
build-eval/llull_eval "$LANG-breccia" --well-typed --variants --n 100000000 --quiet \
    --set breccia_output="$WORK/programs.txt" --set breccia_secs="$secs" \
    --set breccia_bounds="$*" --csv "$OUT"
