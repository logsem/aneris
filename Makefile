TRILLIUM_DIR := 'trillium'
FAIRNESS_DIR := 'fairness'
HL_DIR := 'heap_lang'
LAWYER_DIR := 'lawyer'
LOCAL_SRC_DIRS := $(TRILLIUM_DIR) $(FAIRNESS_DIR) $(HL_DIR) $(LAWYER_DIR)
SRC_DIRS := $(LOCAL_SRC_DIRS) 'external'

ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
VFILES := $(shell find $(LOCAL_SRC_DIRS) -name "*.v")

COQC := coqc
Q:=@

# extract global arguments for Coq from _CoqProject
COQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e 's/-arg ([^ ]*)/\1/g' _CoqProject)

all: $(VFILES:.v=.vo)

.coqdeps.d: $(ALL_VFILES) _CoqProject
	@echo "COQDEP $@"
	$(Q)coqdep -vos -f _CoqProject $(ALL_VFILES) > $@

# do not try to build dependencies if cleaning or just building _CoqProject
ifeq ($(filter clean,$(MAKECMDGOALS)),)
include .coqdeps.d
endif

%.vo: %.v _CoqProject | .coqdeps.d
	@echo "COQC $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) $(COQ_ARGS) -o $@ $<

%.vos: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vos $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vos $(COQ_ARGS) $< -o $@

%.vok: %.v _CoqProject | .coqdeps.d
	@echo "COQC -vok $<"
	$(Q)$(COQC) $(COQPROJECT_ARGS) -vok $(COQ_ARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete
	$(Q)rm -f .lia.cache
	rm -f .coqdeps.d

# project-specific targets
.PHONY: build

VPATH= $(TRILLIUM_DIR) $(FAIRNESS_DIR) $(HL_DIR) $(LAWYER_DIR)
VPATH_FILES := $(shell find $(VPATH) -name "*.v")

build: $(VPATH_FILES:.v=.vo)
