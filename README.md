## Requirements

- x86-64 Linux and Bash
- OCaml 4.14.1
- Python 3.12 with matplotlib 3.6.3
- GNU `/usr/bin/time`, `timeout` and `make`

`bin/breccia` and `bin/egglog` are static x86-64 executables used for the Breccia comparison.

## Build

```bash
make build
```

## Generate terms

Print 100 generated terms:

```bash
build-eval/llull_eval comb --well-typed --n 100 \
  --strategy shell --max-size 6 --max-inst 1 --print-terms
```

Choose `comb` (SysF+Ref/Mut), `fj` (FJ) or `heph` (HephIR). Add `--real-world` to `heph` for the real-world HephIR suite, which uses an extended HephIR. Use `--ill-typed` for ill-typed terms, `--strategy triangle` for enumeration, or `--mode random-fresh --seed 1` for reproducible random generation. `comb-concrete`, `fj-concrete` and `heph-concrete` generate without prototerms.

## Evaluate one setup

```bash
build-eval/llull_eval comb --well-typed --variants --n 100000 \
  --strategy shell --max-size 10 --max-inst 1 --seed 1 \
  --quiet --csv results.csv

python3 experiments/makeChart.py normal results.csv
```

Main options include `--well-typed`, `--ill-typed`, `--strategy`, `--mode`, `--max-size`, `--max-inst`, `--term-time`, `--n`, `--time` and `--max-rss-mb`. See `build-eval/llull_eval --help` for the rest.

## Reproduce the paper

| Paper | Command |
|---|---|
| Fig. 2 | `make fig2` |
| Fig. 3 | `make fig3` |
| Fig. 4 | `make fig4` |
| Fig. 5 | `make fig5` |
| Fig. 6 | `make fig6` |
| Table I and Fig. 7 | `make fig7` |
| Fig. 8 | `make fig8` |

`make all` runs every figure. Runs are skipped when their results already exist, so an interrupted figure can be restarted. Figs. 3–5 also print the FJ numbers quoted in the text.

Random runs use `SEED=195626534` by default. HephIR random runs stop a term after 0.1 s of wall-clock time, so their results vary slightly between machines. Fig. 6 runs for 24 hours; `make fig6 HOURS=0.5` runs a shorter version.

## Make other charts

`experiments/makeChart.py` draws three kinds of chart from a run's `.csv` and `.meta`:

```bash
python3 experiments/makeChart.py normal RUN.csv
python3 experiments/makeChart.py oom RUN.csv
python3 experiments/makeChart.py breccia RUN.csv BRECCIA_RUN.csv
```

`oom` is for runs made with a memory limit (`--max-rss-mb`) instead of a term limit. A Breccia run is made with

```bash
experiments/brecciaRun.sh NAME comb|fj|heph [-u] [bound=value ...]
```

`charts/` holds charts from runs we made, and `charts/runs.tsv` lists the command for each. `make charts RUNS="comb_wt_be_m1 heph_wt_rand_m10"` reruns named entries, and `make charts` reruns all of them.

`make maxinst` runs each language and strategy family at 1, 10 and 100 concrete terms per prototerm (54 runs of 100,000 terms).
