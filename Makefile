FSTAR := fstar.exe
ROOTS := $(wildcard *.fst *.fsti)

CACHEDIR := .cache
OUTDIR := .out
FLAGS += --cache_checked_modules --cache_dir $(CACHEDIR) --odir $(OUTDIR)
#FLAGS += --already_cached Prims,FStar
FLAGS += $(OTHERFLAGS)

all: verify-all

# Dependencies will come from .depend.mk
%.checked:
	$(FSTAR) $(FLAGS) $<
	@touch -c $@ # update timestamp

dep: .depend.mk

include .depend.mk

# The dependency analysis. We call F* on $(ROOTS) to find dependencies
# transitively. The rule also depends on ALL_FST_FILES and
# ALL_FSTI_FILES, to make the analysis run again if anything changes. On
# a first run, both are empty and have no meaning. On a second run, they
# contain the list of all fst/fsti files found on the dependency graph--
# any change to them will trigger a reanalysis.
.depend.mk: $(ROOTS) $(ALL_FST_FILES) $(ALL_FSTI_FILES)
	$(FSTAR) $(FLAGS) --dep full --already_cached Prims,FStar --warn_error -321 $(ROOTS) --output_deps_to $@

.PHONY: dep.graph
dep.graph:
	$(FSTAR) $(FLAGS) --dep graph --warn_error -321 $(ROOTS)
	@# Ignore F* library modules:
	sed -i '/-> "fstar_/d' $@
	sed -i '/-> "prims"/d' $@

# Make a dependency graph of the modules.
dep.pdf: dep.graph
	dot -Tpdf $< > $@

# ALL_CHECKED_FILES is defined by the dependency analysis and output
# to .depend.mk. It includes not only the corresponding .checked for
# every root file, but also the .checked for files that are behind and
# interface, such as LLib.fst in this example.
# 
# This rule must be defined after including .depend.mk so the variable
# is properly defined.
verify-all: $(ALL_CHECKED_FILES)
