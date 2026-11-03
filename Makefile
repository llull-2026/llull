HOURS ?= 24
SEED ?= 195626534
MEM_MB ?= 26112
LAZY_LIMIT ?= 7200
export HOURS SEED MEM_MB LAZY_LIMIT

FIGS = fig2 fig3 fig4 fig5 fig6 fig7 fig8

.PHONY: all build $(FIGS) table1 maxinst charts clean

all: $(FIGS)

build:
	./build.sh

$(FIGS):
	./run_$@.sh

table1: fig7

maxinst:
	experiments/maxInstRuns.sh
	python3 experiments/plotMaxInst.py

charts:
	experiments/galleryRuns.sh $(RUNS)

clean:
	rm -rf build-eval build-lve
