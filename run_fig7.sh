#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

experiments/familyRuns.sh
python3 experiments/plotFig7.py
