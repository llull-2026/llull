#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

TARGET=10000000

rm -rf build
mkdir -p build
cp llull/enumerators.ml llull/generator.ml llull/helper.ml llull/language.ml \
   llull/randomGen.ml langs/comb/combPrograms.ml langs/comb/abstract/*.ml \
   experiments/lazy_vs_eager.ml build/
cd build
ORDER=$(ocamldep -sort *.ml)
ocamlopt -I +unix unix.cmxa -o lazy_vs_eager $ORDER
cd "$ROOT"
echo "built build/lazy_vs_eager"

DATA=output/data
mkdir -p "$DATA"

ulimit -v $((20 * 1024 * 1024))

LAZY_OUT=$(/usr/bin/time -v -o "$DATA/lazy.time" \
    build/lazy_vs_eager comb --lazy --ill-typed --waves 3 --target "$TARGET" \
    --sample 0.25 --csv "$DATA/lazy.csv")
echo "$LAZY_OUT"
LAZY_SECS=$(echo "$LAZY_OUT" | sed -n 's/.* in \([0-9.]*\)s.*/\1/p')
echo "lazy took ${LAZY_SECS}s; running eager with that timeout"

/usr/bin/time -v -o "$DATA/eager.time" \
    build/lazy_vs_eager comb --eager --ill-typed --timeout "$LAZY_SECS" \
    --sample 0.25 --csv "$DATA/eager.csv"

python3 experiments/plot_equalized.py "$DATA" output/sysfrefmut_eager_vs_lazy.png
