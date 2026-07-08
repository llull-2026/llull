## Requirements

- Linux and Bash
- OCaml 4.14.1
- Python 3.12 with matplotlib 3.6.3 and NumPy 1.26.4
- GNU `/usr/bin/time`

## Build

```bash
./build.sh
```

## Generate terms

Print 100 generated terms:

```bash
build-eval/llull_eval comb --well-typed --n 100 \
  --strategy shell --max-size 6 --max-inst 1 --print-terms
```

Choose `fj`, `comb`, `heph`, or `heph2`. Use `--ill-typed` for ill-typed terms or `--mode random-persistent --seed 1` for reproducible random generation.

## Evaluate one setup

```bash
build-eval/llull_eval comb --well-typed --variants --n 100000 \
  --strategy shell --max-size 10 --max-inst 1 --seed 1 \
  --quiet --csv results.csv

python3 experiments/constructPlot.py results.csv
```

Main options include `--well-typed`, `--ill-typed`, `--strategy`, `--mode`, `--max-size`, `--max-inst`, `--n`, and `--time`.

## Reproduce results

```bash
./run_rq1.sh
./run_fig3.sh
./run_fig4.sh
./run_fig5.sh
```

The full experiments require up to 20 GiB of virtual memory. The strategy experiments run 54 configurations of 100,000 terms.
