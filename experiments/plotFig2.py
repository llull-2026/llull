#!/usr/bin/env python3
import bisect
import csv
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mt

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "output", "paper", "data")
DEST = os.path.join(HERE, "..", "output", "paper", "plots")
GREEN, RED = "#10b981", "#ef4444"

RC = {"font.size": 9, "axes.titlesize": 9, "axes.labelsize": 9, "legend.fontsize": 9,
      "xtick.labelsize": 9, "ytick.labelsize": 9}


def series(path):
    rows = list(csv.DictReader(open(path)))
    return [float(r["time"]) for r in rows], [int(r["count"]) for r in rows]


def count_at(ts, cs, t):
    i = bisect.bisect_right(ts, t) - 1
    return cs[i] if i >= 0 else 0


def main():
    plt.rcParams.update(RC)
    os.makedirs(DEST, exist_ok=True)
    lx, ly = series(os.path.join(DATA, "fig2_comb_ill_lazy.csv"))
    ex, ey = series(os.path.join(DATA, "fig2_comb_ill_eager.csv"))
    end = min(lx[-1], ex[-1])

    fig, ax = plt.subplots(figsize=(3.5, 2.45))
    ax.plot(lx, ly, color=GREEN, lw=1.5, label=f"lazy ({ly[-1] / lx[-1] / 1000:.1f}K terms/s)")
    ax.plot(ex, ey, color=RED, lw=1.5, label=f"eager ({ey[-1] / ex[-1] / 1000:.1f}K terms/s)")
    ax.set_xlim(0, end)
    ax.set_ylim(0, None)
    ax.yaxis.set_major_formatter(mt.FuncFormatter(lambda v, _: f"{v / 1e6:g}M" if v else "0"))
    ax.set_xlabel("time (seconds)")
    ax.set_ylabel("total concrete terms generated")
    ax.set_title("SysF+Ref/Mut ill-typed: lazy vs eager")
    ax.grid(True, linestyle=":", alpha=0.5)
    ax.legend(loc="lower right")
    fig.tight_layout(pad=0.3)
    out = os.path.join(DEST, "rq1.png")
    fig.savefig(out, dpi=300)
    plt.close(fig)
    print(f"Wrote {out}")

    n = int(end * 20)
    ts = [end * (i + 0.5) / n for i in range(n)]
    L = [count_at(lx, ly, t) for t in ts]
    E = [count_at(ex, ey, t) for t in ts]
    print(f"run length {end:.2f} s; lazy stopped at {ly[-1]:,} terms, eager at {ey[-1]:,}")
    print(f"lazy rate {ly[-1] / lx[-1] / 1000:.1f}K terms/s, eager rate {ey[-1] / ex[-1] / 1000:.1f}K terms/s")
    print(f"eager behind lazy: {sum(e < l for l, e in zip(L, E)) / n:.1%} of the time")


if __name__ == "__main__":
    main()
