#!/usr/bin/env python3
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from constructPlot import read_meta

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "output", "strategies", "data")
DEST = os.path.join(HERE, "..", "output", "strategies", "plots")

GROUPS = [
    ("comb", "ill", "SysF+Ref/Mut\nill"),
    ("comb", "wt", "SysF+Ref/Mut\nwell"),
    ("fj", "ill", "fj\nill"),
    ("fj", "wt", "fj\nwell"),
    ("heph", "ill", "HephIR\nill"),
    ("heph", "wt", "HephIR\nwell"),
]
FAMILIES = [("rand", "random", "#ef4444"),
            ("enum", "enumeration", "#3b82f6"),
            ("be", "bounded", "#10b981")]
RAND_M = {("comb", "ill"): 1, ("comb", "wt"): 1,
          ("fj", "ill"): 10, ("fj", "wt"): 10,
          ("heph", "ill"): 1, ("heph", "wt"): 10}

RC = {
    "font.size": 18,
    "axes.labelsize": 20,
    "xtick.labelsize": 18,
    "ytick.labelsize": 17,
    "legend.fontsize": 18,
    "legend.title_fontsize": 19,
}


def fraction(lang, kind, family):
    m = RAND_M[(lang, kind)] if family == "rand" else 1
    meta = read_meta(os.path.join(DATA, f"{lang}_{kind}_{family}_m{m}.meta"))
    return int(meta["bugs_found"]) / int(meta["total_bugs"])


def main():
    plt.rcParams.update(RC)
    os.makedirs(DEST, exist_ok=True)

    fig, ax = plt.subplots(figsize=(14, 7))
    width = 0.25
    for fi, (family, label, color) in enumerate(FAMILIES):
        xs = [gi + (fi - 1) * width for gi in range(len(GROUPS))]
        ys = [fraction(lang, kind, family) for lang, kind, _ in GROUPS]
        ax.bar(xs, ys, width, color=color, label=label)
    ax.set_xticks(range(len(GROUPS)), [g[2] for g in GROUPS])
    ax.set_ylabel("bugs found / suite size")
    ax.set_ylim(0, 1.05)
    ax.grid(True, axis="y", linestyle=":", alpha=0.4)
    ax.legend(title="strategy family")

    fig.tight_layout()
    out = os.path.join(DEST, "fig5-families.png")
    fig.savefig(out, dpi=140)
    plt.close(fig)
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
