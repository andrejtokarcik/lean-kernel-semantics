RV_PATH := /home/andrej/Documents/k-project/rv-k/k-distribution/target/release/k/
DEF = lean-kernel
EXT = lean-export
KOMPILE_FLAGS = -O2
# --backend java

include $(RV_PATH)/include/ktest.mak

RUNME ?= runme.lean-export
runme: kompile
	$(KRUN) $(KRUN_FLAGS) -d $(DEFDIR) $(RUNME)
