#!/bin/bash
set -e
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"

experiments/strategyRuns.sh
python3 experiments/plotFamilies.py
