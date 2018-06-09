RV_PATH := /home/andrej/Documents/k-project/rv-k/k-distribution/target/release/k/
DEF = lean-kernel
EXT = lean-export
KOPMILE_FLAGS = -O2

include $(RV_PATH)/include/ktest.mak

RUNME ?= runme.lean-export
runme: kompile
	$(KRUN) $(KRUN_FLAGS) -d $(DEFDIR) $(RUNME)
