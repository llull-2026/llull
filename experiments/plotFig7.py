#!/usr/bin/env python3
import csv
import os

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

from makeChart import read_meta

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "output", "paper", "data")
DEST = os.path.join(HERE, "..", "output", "paper", "plots")
SEED = os.environ.get("SEED", "195626534")

GROUPS = [
    ("comb", "ill", "SysF+\nRef/Mut\nill"),
    ("comb", "wt", "SysF+\nRef/Mut\nwell"),
    ("fj", "ill", "FJ\nill"),
    ("fj", "wt", "FJ\nwell"),
    ("heph", "ill", "HephIR\nill"),
    ("heph", "wt", "HephIR\nwell"),
]
FAMILIES = [("rand", "random", "#ef4444"),
            ("enum", "enumeration", "#3b82f6"),
            ("be", "bounded", "#10b981")]
RAND_M = {("comb", "ill"): 1, ("comb", "wt"): 1,
          ("fj", "ill"): 10, ("fj", "wt"): 10,
          ("heph", "ill"): 1, ("heph", "wt"): 10}

TABLE = [
    ("SysF+Ref/Mut", "comb", {"enum": "triangle", "be": "shell; k<=10", "rand": "FS; k<=8; SP=0.85"}),
    ("FJ", "fj", {"enum": "triangle", "be": "shell; k<=8", "rand": "PP; k<=8; M=10; SP=0.85"}),
    ("HephIR", "heph", {"enum": "triangle", "be": "shell; k<=8", "rand": None}),
]
HEPH_RAND = {"wt": "FS; k<=8; M=10; SP=0.85; 0.1s TL", "ill": "FS; k<=8; SP=0.85; 0.1s TL"}

RC = {"font.size": 8, "axes.labelsize": 8, "xtick.labelsize": 7.5, "ytick.labelsize": 8,
      "legend.fontsize": 8, "legend.title_fontsize": 8}


def run_name(lang, kind, family):
    if family == "rand":
        return f"{lang}_{kind}_rand_m{RAND_M[(lang, kind)]}_s{SEED}"
    return f"{lang}_{kind}_{family}"


def meta(lang, kind, family):
    return read_meta(os.path.join(DATA, run_name(lang, kind, family) + ".meta"))


def table():
    out = os.path.join(DEST, "table1.csv")
    with open(out, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["Generator", "Type", "Search Strategy", "Options", "Bugs Found", "Suite Size", "Terms", "Run"])
        for gen, lang, options in TABLE:
            for kind, word in (("wt", "Well"), ("ill", "Ill")):
                for family, fam in (("enum", "Enum"), ("be", "BE"), ("rand", "Rand")):
                    m = meta(lang, kind, family)
                    opt = options[family] or HEPH_RAND[kind]
                    w.writerow([gen, word, fam, opt, m["bugs_found"], m["total_bugs"], m["total_terms"],
                                run_name(lang, kind, family)])
    print(f"Wrote {out}")
    print(open(out).read())


def main():
    os.makedirs(DEST, exist_ok=True)
    table()
    with plt.rc_context(RC):
        fig, ax = plt.subplots(figsize=(3.5, 2.5))
        width = 0.25
        for fi, (family, label, color) in enumerate(FAMILIES):
            xs = [gi + (fi - 1) * width for gi in range(len(GROUPS))]
            ys = []
            for lang, kind, _ in GROUPS:
                m = meta(lang, kind, family)
                ys.append(int(m["bugs_found"]) / int(m["total_bugs"]))
            ax.bar(xs, ys, width, color=color, label=label)
        ax.set_xticks(range(len(GROUPS)), [g[2] for g in GROUPS])
        ax.set_ylabel("bugs found / suite size")
        ax.set_ylim(0, 1.05)
        ax.grid(True, axis="y", linestyle=":", alpha=0.4)
        ax.legend(title="strategy family", loc="upper right", handlelength=1.2, handletextpad=0.4,
                  borderpad=0.3, borderaxespad=0.2, labelspacing=0.3)
        fig.tight_layout()
        out = os.path.join(DEST, "rq3-families.png")
        fig.savefig(out, dpi=300)
        plt.close(fig)
    print(f"Wrote {out}")


if __name__ == "__main__":
    main()
