#!/usr/bin/env python3
import csv
import os
import re
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

DIFFICULTY_ORDER = ["easy", "medium", "hard"]
COLORS = {"easy": "#10b981", "medium": "#3b82f6", "hard": "#ef4444"}

UNTIERED_COLOR = "#3b82f6"

LANG_CODE = {"comb": "comb", "comb-concrete": "combc",
             "fj": "fj", "fj-concrete": "fjc",
             "heph": "heph", "heph-concrete": "hephc",
             "heph-rw": "hephrw"}
KIND_CODE = {"ill-typed": "it", "well-typed": "wt"}
GEN_CODE = {"enumerate": "en", "random-persistent": "rp", "random-fresh": "rf"}
STRAT_CODE = {"shell": "sh", "naive": "na", "cantor": "ca"}
SCHED_CODE = {"round-robin": "rr", "epoch": "ep", "adaptive": "ad"}

LANG_WORD = {"comb": "combined", "fj": "fj-program", "heph": "heph",
             "heph-rw": "heph-rw"}
GEN_WORD = {"enumerate": "enumeration", "random-persistent": "random walk, persistent",
            "random-fresh": "random walk, from scratch"}


def read_meta(meta_path):
    out = {}
    if not os.path.exists(meta_path):
        return out
    for ln in open(meta_path):
        ln = ln.strip()
        if ln.startswith("#") or ln.startswith("[") or "=" not in ln:
            continue
        k, v = ln.split("=", 1)
        out[k.strip()] = v.strip()
    return out


def meta_for(csv_path):
    return read_meta(os.path.splitext(csv_path)[0] + ".meta")


def tier_lang(meta):
    return "heph_rw" if meta.get("language") == "heph-rw" else meta.get("language", "")


def load(csv_path):
    rows = []
    with open(csv_path) as f:
        for row in csv.DictReader(f):
            row["caught"] = row["caught"].lower() == "true"
            row["iteration"] = int(row["iteration"])
            row["time"] = float(row["time"])
            rows.append(row)
    return rows


def catches_by_difficulty(rows, xkey):
    by_diff = {d: [] for d in DIFFICULTY_ORDER}
    totals = {d: 0 for d in DIFFICULTY_ORDER}
    for r in rows:
        d = r["difficulty"]
        if d not in totals:
            continue
        totals[d] += 1
        if r["caught"]:
            by_diff[d].append(r[xkey])
    for d in DIFFICULTY_ORDER:
        by_diff[d].sort()
    return by_diff, totals


def stacked_curves(rows, max_x, xkey):
    by_diff, totals = catches_by_difficulty(rows, xkey)
    events = sorted({it for d in DIFFICULTY_ORDER for it in by_diff[d]})
    xs = [0] + events + [max_x]
    cum = {d: [] for d in DIFFICULTY_ORDER}
    idx = {d: 0 for d in DIFFICULTY_ORDER}
    count = {d: 0 for d in DIFFICULTY_ORDER}
    for x in xs:
        for d in DIFFICULTY_ORDER:
            cs = by_diff[d]
            while idx[d] < len(cs) and cs[idx[d]] <= x:
                count[d] += 1
                idx[d] += 1
            cum[d].append(count[d])
    caught = {d: len(by_diff[d]) for d in DIFFICULTY_ORDER}
    return xs, cum, caught, totals


def cumulative_curve(rows, max_x, xkey):
    catches = sorted(r[xkey] for r in rows if r["caught"])
    xs = [0] + catches + [max_x]
    ys = []
    count = 0
    idx = 0
    for x in xs:
        while idx < len(catches) and catches[idx] <= x:
            count += 1
            idx += 1
        ys.append(count)
    return xs, ys, len(catches), len(rows)


def _san(v):
    return re.sub(r"[^A-Za-z0-9.]+", "-", str(v))


def _sched_code(meta):
    parts = meta.get("scheduler", "round-robin").split(":")
    base = SCHED_CODE.get(parts[0], parts[0][:2])
    return base + "".join("-" + _san(p) for p in parts[1:])


def short_code(meta):
    lang = LANG_CODE.get(meta.get("language", ""), _san(meta.get("language", "?")))
    kind = KIND_CODE.get(meta.get("term_kind", ""), "?")
    gen = meta.get("generator", "enumerate")
    is_random = gen.startswith("random")
    is_concrete = meta.get("language", "").endswith("-concrete")
    parts = [lang, kind, GEN_CODE.get(gen, gen[:2])]
    if not is_random:
        parts.append(STRAT_CODE.get(meta.get("strategy", "shell"), "sh"))
    parts.append(_sched_code(meta))
    bounds = []
    for key, code in (("max_size", "z"), ("max_depth", "d"), ("max_unique_vars", "u")):
        if meta.get(key):
            bounds.append(code + _san(meta[key]))
    parts.append("".join(bounds) if bounds else "z0")
    mi = meta.get("max_inst", "1")
    if mi and mi != "1" and not is_concrete:
        parts.append("mi" + _san(mi))
    if meta.get("stop_prob"):
        parts.append("sp" + _san(meta["stop_prob"]))
    if meta.get("warmup_steps") and meta["warmup_steps"] != "0":
        parts.append("w" + _san(meta["warmup_steps"]))
    if str(meta.get("inverse_weight", "")).lower() == "true":
        parts.append("iw")
    for pair in meta.get("settings", "").split(";"):
        if "=" in pair:
            k, v = pair.split("=", 1)
            parts.append(k.strip() + "=" + _san(v.strip()))
    return "_".join(parts)


def config_lines(meta):
    lang = meta.get("language", "?")
    l1 = f"{LANG_WORD.get(lang, lang)}, {meta.get('term_kind', '?')}"
    gen = meta.get("generator", "enumerate")
    ms = meta.get("max_size")
    if gen == "enumerate" and ms:
        g = f"bounded-exhaustive {meta.get('strategy', '')} (size ≤ {ms})"
    elif gen == "enumerate":
        g = f"exhaustive enumeration ({meta.get('strategy', '')})"
    else:
        g = GEN_WORD.get(gen, gen)
    sched = meta.get("scheduler", "round-robin")
    l2 = f"{g}  ·  {sched} scheduler  ·  {meta.get('max_inst', '1')} inst/proto-term"
    return l1, l2


def rate_str(meta):
    r = meta.get("generation_rate")
    if not r:
        return None
    try:
        return f"{float(r):,.0f} terms/sec"
    except ValueError:
        return f"{r} terms/sec"


def construct_plot(csv_path, out_dir=None):
    meta = meta_for(csv_path)
    rows = load(csv_path)
    fig, ax = plt.subplots(figsize=(9, 5.5))
    if not rows:
        ax.text(0.5, 0.5, "no data", transform=ax.transAxes, ha="center",
                va="center", color="#64748b")
    elif tier_lang(meta) == "heph_rw":
        max_x = max([r["iteration"] for r in rows]
                    + [int(float(meta["total_terms"]))] if meta.get("total_terms") else
                    [r["iteration"] for r in rows])
        xs, ys, caught, total = cumulative_curve(rows, max_x, "iteration")
        ax.fill_between(xs, 0, ys, step="post", color=UNTIERED_COLOR,
                        alpha=0.8, linewidth=0, label=f"{caught}/{total} caught")
        ax.set_ylim(bottom=0)
        ax.grid(True, linestyle=":", alpha=0.4)
        ax.legend(loc="upper left")
    else:
        max_x = max([r["iteration"] for r in rows]
                    + [int(float(meta["total_terms"]))] if meta.get("total_terms") else
                    [r["iteration"] for r in rows])
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
    l1, l2 = config_lines(meta)
    ax.set_title(f"{l1}\n{l2}", fontsize=11)
    rs = rate_str(meta)
    if rs:
        ax.text(0.98, 0.03, f"generation rate: {rs}", transform=ax.transAxes,
                ha="right", va="bottom", fontsize=9, family="monospace",
                bbox=dict(boxstyle="round", fc="#f8fafc", ec="#cbd5e1", alpha=0.92))
    fig.tight_layout()
    code = short_code(meta) if meta else \
        os.path.splitext(os.path.basename(csv_path))[0]
    out = os.path.join(out_dir or os.path.dirname(os.path.abspath(csv_path)),
                       code + ".png")
    fig.savefig(out, dpi=140)
    plt.close(fig)
    print(f"Wrote {out}")
    return out


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("usage: constructPlot.py <results.csv> [out_dir]")
    construct_plot(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else None)
