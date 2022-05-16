TRILLIUM_DIR := 'trillium'
ANERIS_DIR := 'aneris'
FAIRNESS_DIR := 'fairness'
LOCAL_SRC_DIRS := $(TRILLIUM_DIR) $(ANERIS_DIR) $(FAIRNESS_DIR)
SRC_DIRS := $(LOCAL_SRC_DIRS) 'external'

ALL_VFILES := $(shell find $(SRC_DIRS) -name "*.v")
VFILES := $(shell find $(LOCAL_SRC_DIRS) -name "*.v")
TRILLIUM_VFILES := $(shell find $(TRILLIUM_DIR) -name "*.v")
FAIRNESS_VFILES := $(shell find $(FAIRNESS_DIR) -name "*.v")
ANERIS_VFILES := $(shell find $(ANERIS_DIR) -name "*.v")

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
.PHONY: clean-trillium clean-fairness clean-aneris trillium fairness aneris

clean-trillium:
	@echo "CLEAN vo glob aux"
	$(Q)find  $(TRILLIUM_DIR) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete
clean-fairness:
	@echo "CLEAN vo glob aux"
	$(Q)find  $(FAIRNESS_DIR) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete

clean-aneris:
	@echo "CLEAN vo glob aux"
	$(Q)find $(ANERIS_DIR) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete

trillium: $(TRILLIUM_VFILES:.v=.vo)

fairness: $(FAIRNESS_VFILES:.v=.vo)

aneris: $(ANERIS_VFILES:.v=.vo)

.PHONY: default
