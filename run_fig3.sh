#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

./build.sh
export DATA=output/paper/data
mkdir -p "$DATA"

experiments/brecciaRun.sh comb_wt_breccia-u-e8 comb -u esize=8 tsize=2 varid=1
experiments/brecciaRun.sh fj_wt_breccia-u-nm-e4-c3-d2 fj -u nummethods=0 esize=4 numclasses=3 classdepth=2

python3 experiments/plotFig3to5.py breccia
