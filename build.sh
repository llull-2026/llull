#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

SRC=$(find llull langs -name '*.ml')

build() {
    local out=$1 exe=$2; shift 2
    rm -rf "$out"
    mkdir -p "$out"
    cp "$@" "$out/"
    (cd "$out" && ocamlopt -I +unix unix.cmxa -o "$exe" $(ocamldep -sort *.ml))
    echo "built $out/$exe"
}

build build-eval llull_eval $SRC
build build-lve lazy_vs_eager $(echo $SRC | tr ' ' '\n' | grep -v '/evaluator.ml$') experiments/lazy_vs_eager.ml
