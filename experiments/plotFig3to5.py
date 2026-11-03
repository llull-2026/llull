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
COLORS = {"easy": "#10b981", "medium": "#3b82f6", "hard": "#ef4444"}
DIFFS = ["easy", "medium", "hard"]
TERMS = 500000

RUNS = {
    "breccia": ("comb_wt_breccia-u-e8", "fj_wt_breccia-u-nm-e4-c3-d2", "Breccia", "rq2-sysf-breccia.png"),
    "concrete": ("comb_wt_be_concrete", "fj_wt_be_concrete", "concrete", "rq2-sysf-llull-concrete.png"),
    "prototerm": ("comb_wt_be", "fj_wt_be", "prototerm", "rq2-sysf-llull-prototerms.png"),
}

RC = {"font.size": 9, "axes.titlesize": 9, "axes.labelsize": 9, "xtick.labelsize": 8.5,
      "ytick.labelsize": 8.5, "legend.fontsize": 7.5, "legend.title_fontsize": 7.5}
K = mt.FuncFormatter(lambda v, _: f"{v / 1e3:g}K" if v >= 1000 else f"{v:g}")


def path(name):
    return os.path.join(DATA, name)


def rate_str(r):
    return f"{r:,.0f} terms/sec" if r >= 10 else f"{r:.2f} terms/sec"


def stacked(name, title, top, out, xmax, legend):
    m = read_meta(path(name) + ".meta")
    caught, totals = read_catches(path(name) + ".csv")
    terms = int(m["total_terms"])
    xs = sorted({0, terms} | {t for t, _ in caught})
    fig, ax = plt.subplots(figsize=(3.5, 2.6))
    base = [0] * len(xs)
    for d in DIFFS:
        got = [t for t, dd in caught if dd == d]
        tops = [b + sum(t <= x for t in got) for b, x in zip(base, xs)]
        ax.fill_between(xs, base, tops, step="post", color=COLORS[d], alpha=0.8, lw=0,
                        label=f"{d} {len(got)}/{totals[d]}")
        base = tops
    ax.set_xlim(0, xmax or terms)
    ax.set_ylim(0, top)
    ax.xaxis.set_major_formatter(K)
    ax.grid(True, linestyle=":", alpha=0.4)
    ax.legend(**legend, title="difficulty (caught/total)", framealpha=0.9)
    ax.set_xlabel("Terms generated")
    ax.set_ylabel("Cumulative bugs caught")
    ax.set_title(title)
    y = len(caught) / top + 0.04 if len(caught) / top < 0.25 else 0.04
    ax.text(0.98, y, f"generation rate: {rate_str(float(m['generation_rate']))}", transform=ax.transAxes,
            ha="right", va="bottom", family="monospace", fontsize=7,
            bbox=dict(boxstyle="round", fc="#f8fafc", ec="#cbd5e1", alpha=0.92))
    fig.tight_layout(pad=0.3)
    fig.savefig(out, dpi=300)
    plt.close(fig)
    print(f"Wrote {out}")


def summary(lang):
    for kind, (comb, fj, label, _) in RUNS.items():
        name = comb if lang == "comb" else fj
        m = read_meta(path(name) + ".meta")
        if m:
            print(f"{lang} {label}: {m['bugs_found']}/{m['total_bugs']} bugs, "
                  f"{float(m['generation_rate']):,.2f} terms/sec, {int(m['total_terms']):,} terms")
    rates = {k: float(read_meta(path(v[0 if lang == "comb" else 1]) + ".meta").get("generation_rate", 0))
             for k, v in RUNS.items()}
    if rates["breccia"]:
        for k in ("concrete", "prototerm"):
            if rates[k]:
                print(f"{lang} {k} rate / Breccia rate: {rates[k] / rates['breccia']:,.1f}x")


def main():
    which = sys.argv[1:] or list(RUNS)
    plt.rcParams.update(RC)
    os.makedirs(DEST, exist_ok=True)
    found = [int(read_meta(path(v[0]) + ".meta").get("bugs_found", 0)) for v in RUNS.values()]
    top = max(found) * 1.08
    for kind in which:
        comb, _, label, fname = RUNS[kind]
        legend = (dict(loc="lower right", bbox_to_anchor=(0.98, 0.17), borderaxespad=0)
                  if kind == "prototerm" else dict(loc="upper left"))
        xmax = None if kind == "breccia" else TERMS
        stacked(comb, f"SysF+Ref/Mut well-typed: {label}", top, os.path.join(DEST, fname), xmax, legend)
    summary("comb")
    summary("fj")


if __name__ == "__main__":
    main()
