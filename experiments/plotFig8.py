#!/usr/bin/env python3
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import matplotlib.ticker as mt

from makeChart import read_meta, read_catches

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "output", "paper", "data")
DEST = os.path.join(HERE, "..", "output", "paper", "plots")

RC = {"font.size": 8, "axes.labelsize": 8, "xtick.labelsize": 8, "ytick.labelsize": 8,
      "legend.fontsize": 7, "legend.title_fontsize": 8}


def main():
    well, ill = sys.argv[1], sys.argv[2]
    plt.rcParams.update(RC)
    os.makedirs(DEST, exist_ok=True)
    w = [t for t, _ in read_catches(os.path.join(DATA, well + ".csv"))[0]]
    i = [t for t, _ in read_catches(os.path.join(DATA, ill + ".csv"))[0]]
    mw, mi = read_meta(os.path.join(DATA, well + ".meta")), read_meta(os.path.join(DATA, ill + ".meta"))
    end = int(mw["total_terms"]) + int(mi["total_terms"])
    events = sorted({0, end} | {2 * n for n in w} | {2 * n - 1 for n in i})
    cw = [sum(2 * n <= x for n in w) for x in events]
    ci = [sum(2 * n - 1 <= x for n in i) for x in events]
    fig, ax = plt.subplots(figsize=(3.5, 2.4))
    ax.fill_between(events, 0, cw, step="post", color="#4a7cf0", lw=0,
                    label=f"well-typed (wrongly-rejects)  {mw['bugs_found']}/{mw['total_bugs']}")
    ax.fill_between(events, cw, [a + b for a, b in zip(cw, ci)], step="post", color="#fb8c3c", lw=0,
                    label=f"ill-typed (wrongly-accepts)  {mi['bugs_found']}/{mi['total_bugs']}")
    ax.set_xlim(0, end)
    ax.xaxis.set_major_formatter(mt.FuncFormatter(
        lambda v, _: f"{v / 1e6:g}M" if v >= 1e6 else (f"{v / 1e3:g}K" if v else "0")))
    ax.set_ylim(0, (len(w) + len(i)) * 1.05)
    ax.set_xlabel("Terms generated (alternating well-/ill-typed)")
    ax.set_ylabel("Cumulative bugs caught")
    ax.grid(True, linestyle=":", alpha=0.4)
    ax.legend(title=f"{len(w) + len(i)}/{int(mw['total_bugs']) + int(mi['total_bugs'])} bugs caught",
              loc="lower right", framealpha=0.95)
    fig.tight_layout(pad=0.3)
    out = os.path.join(DEST, "rq4.png")
    fig.savefig(out, dpi=300)
    plt.close(fig)
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
