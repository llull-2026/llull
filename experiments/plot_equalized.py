import csv, os, re, sys
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

def load(path):
    xs, ys = [], []
    with open(path) as f:
        r = csv.reader(f)
        next(r)
        for row in r:
            xs.append(float(row[0]))
            ys.append(int(row[1]))
    return xs, ys

def peak_gb(path):
    if not os.path.exists(path):
        return None
    with open(path) as f:
        m = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", f.read())
    return int(m.group(1)) / 1048576 if m else None

data_dir = sys.argv[1]
out = sys.argv[2]

lx, ly = load(data_dir + "/lazy.csv")
ex, ey = load(data_dir + "/eager.csv")

lazy_peak = peak_gb(data_dir + "/lazy.time")
eager_peak = peak_gb(data_dir + "/eager.time")

xmax = max(lx[-1], ex[-1])

lazy_rate = ly[-1] / xmax / 1000.0
eager_rate = ey[-1] / xmax / 1000.0

def extend(xs, ys):
    if xs[-1] < xmax:
        xs = xs + [xmax]
        ys = ys + [ys[-1]]
    return xs, ys

def label(name, peak, rate):
    if peak is None:
        return "%s (%.1fk terms/s)" % (name, rate)
    return "%s (peak %.1f GB, %.1fk terms/s)" % (name, peak, rate)

lx, ly = extend(lx, ly)
ex, ey = extend(ex, ey)

fig, ax = plt.subplots(figsize=(9, 5.5))
ax.plot(lx, ly, label=label("lazy", lazy_peak, lazy_rate), color="#1f77b4")
ax.plot(ex, ey, label=label("eager", eager_peak, eager_rate), color="#d62728")
ax.set_xlabel("time (seconds)")
ax.set_ylabel("total concrete terms generated")
ax.set_title("sysF+ref/mut: concrete-term output over time")
ax.legend()
ax.grid(True, alpha=0.3)
fig.tight_layout()
fig.savefig(out, dpi=130)
print("wrote", out)
