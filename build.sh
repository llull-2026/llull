#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

OUT=build-eval
mkdir -p "$OUT"
cp llull/*.ml \
   langs/fj/fjPrograms.ml langs/fj/abstract/*.ml langs/fj/bug-suite/*.ml \
   langs/fj/concrete/*.ml \
   langs/comb/combPrograms.ml langs/comb/abstract/*.ml \
   langs/comb/bug-suite/*.ml langs/comb/concrete/*.ml \
   langs/heph/hephPrograms.ml langs/heph/abstract/*.ml \
   langs/heph/bug-suite/*.ml langs/heph2/abstract/*.ml \
   "$OUT/"
cd "$OUT"
ORDER=$(ocamldep -sort *.ml)
ocamlopt -I +unix unix.cmxa -o llull_eval $ORDER
echo "built $OUT/llull_eval"
