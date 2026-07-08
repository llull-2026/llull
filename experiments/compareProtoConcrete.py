#!/usr/bin/env python3
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from constructPlot import (load, stacked_curves, meta_for, short_code,
                           rate_str, COLORS, DIFFICULTY_ORDER)

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "output", "rq2compare", "data")
DEST = os.path.join(HERE, "..", "output", "rq2compare", "plots")

DISPLAY = {"comb": "SysF+Ref/Mut", "fj": "fj"}

RC = {
    "font.size": 24,
    "axes.titlesize": 28,
    "axes.labelsize": 26,
    "xtick.labelsize": 22,
    "ytick.labelsize": 22,
    "legend.fontsize": 22,
    "legend.title_fontsize": 23,
    "figure.titlesize": 32,
}


def render_ax(ax, csv_path, title):
    rows = load(csv_path)
    max_x = max(r["iteration"] for r in rows)
    meta = meta_for(csv_path)
    if meta.get("total_terms"):
        max_x = max(max_x, int(meta["total_terms"]))
    xs, cum, caught, totals = stacked_curves(rows, max_x, "iteration")
    baseline = [0] * len(xs)
    for d in DIFFICULTY_ORDER:
        top = [b + c for b, c in zip(baseline, cum[d])]
        if totals[d]:
            ax.fill_between(xs, baseline, top, step="post", color=COLORS[d],
                            alpha=0.8, linewidth=0,
                            label=f"{d} {caught[d]}/{totals[d]}")
        baseline = top
    ax.set_ylim(bottom=0)
    ax.grid(True, linestyle=":", alpha=0.4)
    ax.legend(loc="upper left", title="difficulty (caught/total)")
    ax.set_xlabel("Terms generated")
    ax.set_ylabel("Cumulative bugs caught")
    ax.set_title(title)
    rs = rate_str(meta)
    if rs:
        ax.text(0.98, 0.03, f"generation rate: {rs}", transform=ax.transAxes,
                ha="right", va="bottom", family="monospace",
                bbox=dict(boxstyle="round", fc="#f8fafc", ec="#cbd5e1", alpha=0.92))


def main():
    plt.rcParams.update(RC)
    os.makedirs(DEST, exist_ok=True)

    rows = [
        ("fj", "fj_wt_be_m1.csv", "fj_wt_be_concrete.csv"),
        ("comb", "comb_wt_be_m1.csv", "comb_wt_be_concrete.csv"),
    ]

    fig, axes = plt.subplots(2, 2, figsize=(28, 17))
    for ri, (lang, proto, concrete) in enumerate(rows):
        name = DISPLAY[lang]
        pp = os.path.join(DATA, proto)
        cp = os.path.join(DATA, concrete)
        render_ax(axes[ri][0], pp, f"{name} · well-typed — prototerm")
        render_ax(axes[ri][1], cp, f"{name} · well-typed — concrete")
        row_top = max(axes[ri][0].get_ylim()[1], axes[ri][1].get_ylim()[1])
        axes[ri][0].set_ylim(0, row_top)
        axes[ri][1].set_ylim(0, row_top)

    fig.tight_layout()

    code = f"compare_wt_be_fj-{short_code(meta_for(os.path.join(DATA, rows[0][1])))}" \
           f"_comb-{short_code(meta_for(os.path.join(DATA, rows[1][1])))}.png"
    out = os.path.join(DEST, code)
    fig.savefig(out, dpi=140)
    plt.close(fig)
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
