#!/usr/bin/env python3
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from makeChart import read_meta

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "output", "charts", "maxinst")
DEST = os.path.join(HERE, "..", "output", "charts")

MS = [1, 10, 100]
FAMILIES = [("enum", "enumeration"), ("be", "bounded"), ("rand", "random")]
SERIES = [
    ("comb", "ill", "SysF+Ref/Mut/ill", "tab:blue"),
    ("comb", "wt", "SysF+Ref/Mut/well", "tab:orange"),
    ("fj", "ill", "FJ/ill", "tab:green"),
    ("fj", "wt", "FJ/well", "tab:red"),
    ("heph", "ill", "HephIR/ill", "tab:purple"),
    ("heph", "wt", "HephIR/well", "tab:brown"),
]

RC = {
    "font.size": 18,
    "axes.titlesize": 22,
    "axes.labelsize": 20,
    "xtick.labelsize": 17,
    "ytick.labelsize": 17,
    "legend.fontsize": 17,
}


def bugs_found(lang, kind, family, m):
    meta = read_meta(os.path.join(DATA, f"{lang}_{kind}_{family}_m{m}.meta"))
    return int(meta["bugs_found"])


def main():
    plt.rcParams.update(RC)
    os.makedirs(DEST, exist_ok=True)

    fig, axes = plt.subplots(1, 3, figsize=(24, 8))
    for ax, (family, title) in zip(axes, FAMILIES):
        for lang, kind, label, color in SERIES:
            base = bugs_found(lang, kind, family, 1)
            ys = [bugs_found(lang, kind, family, m) / base for m in MS]
            ax.plot(MS, ys, marker="o", color=color, label=label)
        ax.axhline(1.0, linestyle="--", linewidth=1, color="#7a9cc4")
        ax.set_xscale("log")
        ax.set_xticks(MS, [str(m) for m in MS])
        ax.set_xlabel("max_inst")
        ax.set_ylabel("bugs found ÷ bugs at m1")
        ax.set_title(title)
        ax.grid(True, linestyle=":", alpha=0.4)
        ax.legend()

    fig.tight_layout()
    out = os.path.join(DEST, "maxinst.png")
    fig.savefig(out, dpi=140)
    plt.close(fig)
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
