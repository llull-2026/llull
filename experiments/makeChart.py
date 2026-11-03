#!/usr/bin/env python3
import argparse
import csv
import os
from collections import Counter

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter, MaxNLocator

LANG_WORD = {"comb": "SysF+Ref/Mut", "fj": "FJ", "heph": "HephIR"}
DIFFS = ["easy", "medium", "hard"]
COLOR = {"easy": "#3fc495", "medium": "#5f9cf5", "hard": "#ef6a6a"}
X_MAX = 100_000

csv.field_size_limit(10 ** 9)


def run_path(arg):
    return arg[:-4] if arg.endswith(".csv") else arg


def read_meta(path):
    meta = {}
    if not os.path.exists(path):
        return meta
    for line in open(path):
        if " = " in line and not line.startswith("#"):
            k, v = line.rstrip("\n").split(" = ", 1)
            meta[k.strip()] = v.strip()
    return meta


def read_catches(csv_path):
    caught, totals = [], Counter()
    with open(csv_path, newline="") as f:
        for row in csv.DictReader(f):
            d = row["difficulty"]
            totals[d] += 1
            if row["caught"] == "true":
                caught.append((int(row["iteration"]), d))
    caught.sort()
    return caught, totals


def is_real_world(meta):
    return meta.get("real_world") == "true"


def lang_label(meta):
    lang = meta.get("language", "?")
    for suffix in ("-concrete", "-breccia"):
        if lang.endswith(suffix):
            lang = lang[:-len(suffix)]
    word = LANG_WORD.get(lang, lang)
    return word + " real-world" if is_real_world(meta) else word


def gen_label(meta):
    g = meta.get("generator", "")
    if g == "enumerate":
        strategy = meta.get("strategy", "")
        if strategy == "shell" and meta.get("max_size"):
            s = "bounded-exhaustive"
        elif strategy == "triangle":
            s = "enumerated"
        else:
            s = f"enumerated ({strategy})"
        if meta.get("dovetail") == "true":
            s += ", dovetailed groundings"
    elif g == "random-fresh":
        s = "random from scratch"
    elif g == "random-persistent":
        s = "random cumulative"
    elif g == "breccia":
        s = "Breccia"
    else:
        s = g
    if meta.get("language", "").endswith("-concrete"):
        s += ", concrete terms"
    return s


def settings_label(meta, extra=()):
    parts = []
    if meta.get("generator") == "breccia":
        bounds = dict(kv.split("=", 1) for kv in meta.get("settings", "").split(";") if "=" in kv)
        if bounds.get("breccia_bounds"):
            parts.append(bounds["breccia_bounds"])
    else:
        if meta.get("max_size"):
            parts.append(f"max size {meta['max_size']}")
        if not meta.get("language", "").endswith("-concrete") and meta.get("max_inst"):
            parts.append(f"max_inst {meta['max_inst']}")
        if meta.get("stop_prob"):
            parts.append(f"stop prob {meta['stop_prob']}")
        if meta.get("term_time"):
            parts.append(f"per-term limit {meta['term_time']} s")
        if meta.get("inverse_weight") == "true":
            parts.append("inverse weight")
        if meta.get("warmup_steps") not in (None, "", "0"):
            parts.append(f"warmup {meta['warmup_steps']}")
        if meta.get("seed") and meta.get("generator", "").startswith("random"):
            parts.append(f"seed {meta['seed']}")
    parts.extend(extra)
    return ", ".join(parts)


def title_for(meta, extra=()):
    s = settings_label(meta, extra)
    return f"{lang_label(meta)} · {meta.get('term_kind', '?')} · {gen_label(meta)}" + (f" ({s})" if s else "")


def fmt_mem_kb(kb):
    if not kb:
        return None
    kb = int(kb)
    return f"peak memory: {kb / 1024 / 1024:.1f} GB" if kb >= 1024 * 1024 else f"peak memory: {kb / 1024:.0f} MB"


def fmt_rate(meta):
    r = meta.get("generation_rate")
    if not r:
        return "generation rate: not recorded"
    r = float(r)
    return f"generation rate: {r:,.0f} terms/sec" if r >= 10 else f"generation rate: {r:.2f} terms/sec"


def kfmt(x, _):
    if x >= 1e6:
        return f"{x / 1e6:g}M"
    return f"{x / 1e3:g}K" if x >= 1e3 else f"{x:g}"


def steps(caught, x_end):
    xs, ys, n = [0], [0], 0
    for it, _ in caught:
        if it > x_end:
            break
        n += 1
        xs.append(it)
        ys.append(n)
    xs.append(x_end)
    ys.append(n)
    return xs, ys


def stacked(ax, caught, x_end, single=False):
    if single:
        xs, ys = steps(caught, x_end)
        ax.fill_between(xs, 0, ys, step="post", color=COLOR["medium"], lw=0)
        return
    pts = sorted({0, x_end} | {it for it, _ in caught if it <= x_end})
    base = [0] * len(pts)
    for d in DIFFS:
        its = sorted(it for it, dd in caught if dd == d)
        ys, j = [], 0
        for p in pts:
            while j < len(its) and its[j] <= p:
                j += 1
            ys.append(j)
        top = [b + y for b, y in zip(base, ys)]
        ax.fill_between(pts, base, top, step="post", color=COLOR[d], lw=0)
        base = top


def diff_legend(ax, caught, totals, x_end, single=False):
    found = Counter(d for it, d in caught if it <= x_end)
    if single:
        return ax.legend([plt.Rectangle((0, 0), 1, 1, color=COLOR["medium"])],
                         [f"bugs found {sum(found.values())}/{sum(totals.values())}"],
                         loc="upper left", fontsize=9, handlelength=1.2, framealpha=0.9)
    handles = [plt.Rectangle((0, 0), 1, 1, color=COLOR[d]) for d in reversed(DIFFS)]
    labels = [f"{d} {found[d]}/{totals[d]}" for d in reversed(DIFFS)]
    return ax.legend(handles, labels, title="difficulty (found/total)", loc="upper left", fontsize=9,
                     title_fontsize=9, handlelength=1.2, framealpha=0.9)


def info_box(ax, lines):
    lines = [l for l in lines if l]
    ax.text(0.98, 0.03, "\n".join(lines), transform=ax.transAxes, ha="right", va="bottom",
            fontsize=9, family="monospace",
            bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="#bbb", alpha=0.92))


def finish(ax, title, x_end):
    ax.set_title(title, loc="left", fontsize=11)
    ax.set_xlabel("terms generated")
    ax.set_ylabel("cumulative bugs found")
    ax.set_xlim(0, x_end)
    ax.set_ylim(bottom=0)
    ax.xaxis.set_major_formatter(FuncFormatter(kfmt))
    ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    ax.grid(alpha=0.25)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


def save(fig, out):
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    fig.savefig(out, dpi=150, bbox_inches="tight", facecolor="white")
    plt.close(fig)
    print(f"Wrote {out}")


def normal(run, out, x_max=None, notes=()):
    meta = read_meta(run + ".meta")
    caught, totals = read_catches(run + ".csv")
    x_end = x_max or int(meta.get("total_terms") or X_MAX)
    single = is_real_world(meta)
    fig, ax = plt.subplots(figsize=(8, 4.6))
    stacked(ax, caught, x_end, single)
    finish(ax, title_for(meta, notes), x_end)
    diff_legend(ax, caught, totals, x_end, single)
    info_box(ax, [fmt_rate(meta), fmt_mem_kb(meta.get("peak_rss_kb"))])
    save(fig, out)


def oom(run, out, notes=()):
    meta = read_meta(run + ".meta")
    caught, totals = read_catches(run + ".csv")
    x_end = int(meta["total_terms"])
    single = is_real_world(meta)
    fig, ax = plt.subplots(figsize=(8, 4.6))
    stacked(ax, caught, x_end, single)
    finish(ax, title_for(meta, ["run to memory limit", *notes]), x_end)
    diff_legend(ax, caught, totals, x_end, single)
    info_box(ax, [fmt_rate(meta), fmt_mem_kb(meta.get("peak_rss_kb")),
                  f"{x_end:,} terms in {float(meta['total_time']) / 3600:.1f} h",
                  meta.get("stop_reason") and f"stop: {meta['stop_reason']}"])
    save(fig, out)


def breccia_mem(run):
    path = run + ".mem"
    return open(path).read().split()[0] if os.path.exists(path) else None


def breccia(run, others, out, x_max=None, notes=()):
    meta = read_meta(run + ".meta")
    caught, totals = read_catches(run + ".csv")
    x_end = x_max or X_MAX
    colors = ["#d9730d", "#CC79A7", "#56B4E9", "#000000", "#999999"]
    fig, ax = plt.subplots(figsize=(8, 4.6))
    xs, ys = steps(caught, x_end)

    def found(c):
        f = Counter(d for it, d in c if it <= x_end)
        return " / ".join(f"{f[d]}" for d in DIFFS)

    ax.step(xs, ys, where="post", color="#1f4e8c", lw=2,
            label=f"Llull {gen_label(meta)}: {ys[-1]}  (easy/med/hard {found(caught)})")
    lines = ["Llull   " + fmt_rate(meta), "        " + (fmt_mem_kb(meta.get("peak_rss_kb")) or "")]
    for (label, brun), color in zip(others, colors):
        bm = read_meta(brun + ".meta")
        bc, _ = read_catches(brun + ".csv")
        n = int(bm.get("total_terms") or x_end)
        bx, by = steps(bc, min(n, x_end))
        ax.step(bx, by, where="post", ls="--", color=color, lw=2,
                label=f"Breccia {label}: {by[-1]}  (easy/med/hard {found(bc)})" +
                      ("" if n >= x_end else f"\nBreccia ran out of terms at {n:,}"))
        lines += ["Breccia " + fmt_rate(bm), "        " + (fmt_mem_kb(breccia_mem(brun)) or "")]
    extra = [f"vs Breccia {others[0][0]}"] if len(others) == 1 else ["vs Breccia"]
    finish(ax, title_for(meta, extra + list(notes)), x_end)
    ax.legend(loc="upper left", bbox_to_anchor=(0, -0.13), fontsize=8, frameon=False,
              title=f"bugs found (suite: easy/med/hard {' / '.join(str(totals[d]) for d in DIFFS)})",
              title_fontsize=8)
    info_box(ax, [l for l in lines if l.strip()])
    save(fig, out)


def main():
    p = argparse.ArgumentParser(prog="makeChart.py")
    sub = p.add_subparsers(dest="format", required=True)
    for name in ("normal", "oom", "breccia"):
        s = sub.add_parser(name)
        s.add_argument("run")
        if name == "breccia":
            s.add_argument("breccia_runs", nargs="+", metavar="BRECCIA_RUN[=LABEL]")
        if name != "oom":
            s.add_argument("--x-max", type=int)
        s.add_argument("--note", action="append", default=[])
        s.add_argument("-o", "--out")
    a = p.parse_args()
    run = run_path(a.run)
    out = a.out or run + ".png"
    if a.format == "normal":
        normal(run, out, a.x_max, a.note)
    elif a.format == "oom":
        oom(run, out, a.note)
    else:
        others = []
        for b in a.breccia_runs:
            path, _, label = b.partition("=")
            path = run_path(path)
            if not label:
                bm = read_meta(path + ".meta")
                label = settings_label(bm) or os.path.basename(path)
            others.append((label, path))
        breccia(run, others, out, a.x_max, a.note)


if __name__ == "__main__":
    main()
