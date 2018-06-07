RV_PATH = /home/andrej/Documents/k-project/rv-k/k-distribution/target/release/k/
RV_KOMPILE := $(RV_PATH)/bin/kompile
RV_KRUN := $(RV_PATH)/bin/krun
RV_KAST := $(RV_PATH)/bin/kast

LEANOUT ?= test.leanout

.PHONY: all lean run ast

all: lean run

lean : lean-kompiled/timestamp
lean-kompiled/timestamp : lean.k
	$(RV_KOMPILE) -v -O2 lean.k

run : lean
	$(RV_KRUN) -v $(LEANOUT)

ast : lean
	$(RV_KAST) -v $(LEANOUT)
