#!/usr/bin/env python3
import csv
import math
import os
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from makeChart import read_meta

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "output", "paper", "data")
DEST = os.path.join(HERE, "..", "output", "paper", "plots")
WIDTH = 300.0

RC = {"font.size": 9, "axes.titlesize": 9, "axes.labelsize": 9,
      "xtick.labelsize": 8.5, "ytick.labelsize": 8.5}


def cumulative(rows):
    out = sorted((float(t), int(c)) for t, c in rows)
    return [(0.0, 0)] + out if not out or out[0][0] > 0 else out


def count_at(series, t, start=0):
    i = start
    while i + 1 < len(series) and series[i + 1][0] <= t:
        i += 1
    return series[i][1], i


def rates(series, width):
    end = series[-1][0]
    n = max(1, int(math.floor(end / width)))
    out, hint = [], 0
    prev, hint = count_at(series, 0.0, hint)
    for k in range(n):
        c, hint = count_at(series, (k + 1) * width, hint)
        out.append(((k + 0.5) * width, (c - prev) / width))
        prev = c
    return out


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else "heph_wt_enum_24h"
    run = os.path.join(DATA, name)
    plt.rcParams.update(RC)
    os.makedirs(DEST, exist_ok=True)
    m = read_meta(run + ".meta")
    series = cumulative([(r["time"], r["terms"]) for r in csv.DictReader(open(run + ".trace.csv"))])
    width = min(WIDTH, max(series[-1][0] / 20, 1.0))
    buckets = rates(series, width)
    vals = [r for _, r in buckets]
    avg = series[-1][1] / series[-1][0]

    fig, ax = plt.subplots(figsize=(3.5, 2.45))
    ax.plot([t / 3600 for t, _ in buckets], vals, color="#10b981", lw=1.0)
    ax.set_xlim(0, series[-1][0] / 3600)
    ax.set_ylim(0, max(vals) * 1.3)
    ax.set_xlabel("time (hours)")
    label = "5 min" if width == WIDTH else f"{width:.0f} s"
    ax.set_ylabel(f"terms/sec ({label} buckets)")
    ax.set_title("HephIR well-typed: enumerated")
    ax.grid(True, linestyle=":", alpha=0.5)
    ax.text(0.98, 0.95, f"average rate: {avg:,.0f} terms/sec\npeak memory: {int(m['peak_rss_kb']) / 1048576:.1f} GB",
            transform=ax.transAxes, ha="right", va="top", family="monospace", fontsize=7,
            bbox=dict(boxstyle="round", fc="#f8fafc", ec="#cbd5e1", alpha=0.92))
    fig.tight_layout(pad=0.3)
    out = os.path.join(DEST, "rq2-hephir-generation-rate-over-time.png")
    fig.savefig(out, dpi=300)
    plt.close(fig)
    print(f"Wrote {out}")
    print(f"{int(m['total_terms']):,} terms in {float(m['total_time']) / 3600:.1f} h, "
          f"{m['bugs_found']}/{m['total_bugs']} bugs, stop: {m.get('stop_reason')}")


if __name__ == "__main__":
    main()
