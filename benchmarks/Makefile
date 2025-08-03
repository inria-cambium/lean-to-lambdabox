comma:= ,
empty:=
space:= $(empty) $(empty)

bin:=bin
results:=results
backends=lean\
malfunction-reference\
malfunction-flambda-O0\
malfunction-flambda-O3\
malfunction-noflambda\
malfunction-sekarray\
malfunction-unsafearray\
malfunction-prune-nounbox\
malfunction-noprune-unbox\
malfunction-noprune-nounbox\
malfunction-noinline

benches:=
define register_test
$(let testname harness rest,$(subst :, ,$(1)),\
ifeq ($(harness),natio)
# In this case, the test is a benchmark we want to run and $(rest) is an input value which gives a reasonable benchmark runtime.
# We add a version to run with 0 in order to have a sensible baseline.
benches+=$(testname):0
benches+=$(testname):$(rest)
endif
)
endef

$(foreach testspec,$(shell cat TESTS),$(eval $(call register_test,$(testspec))))

default:
	$(error No target specified)

FORCE:

$(bin)/lean/%: FORCE | $(bin)/lean/
	make -C via_lean bin/$* TARGETDIR=../$(bin)/lean

$(bin)/malfunction-reference/%: FORCE | $(bin)/malfunction-reference/
	OCAMLPARAM=_,O2=1 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-reference

$(bin)/malfunction-flambda-O0/%: FORCE | $(bin)/malfunction-flambda-O0/
	make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-flambda-O0

$(bin)/malfunction-flambda-O3/%: FORCE | $(bin)/malfunction-flambda-O3/
	OCAMLPARAM=_,O3=1 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-flambda-O3

$(bin)/malfunction-noflambda/%: FORCE | $(bin)/malfunction-noflambda/
	FLAMBDA=0 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-noflambda

$(bin)/malfunction-sekarray/%: FORCE | $(bin)/malfunction-sekarray/
	ARRAYML=SekArray.ml OCAMLPARAM=_,O2=1 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-sekarray

$(bin)/malfunction-unsafearray/%: FORCE | $(bin)/malfunction-unsafearray/
	ARRAYML=UnsafeArray.ml OCAMLPARAM=_,O2=1 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-unsafearray

$(bin)/malfunction-prune-nounbox/%: FORCE | $(bin)/malfunction-prune-nounbox/
	UNBOX=0 OCAMLPARAM=_,O2=1 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-prune-nounbox

$(bin)/malfunction-noprune-unbox/%: FORCE | $(bin)/malfunction-noprune-unbox/
	PRUNE_CONSTRUCTORS=0 OCAMLPARAM=_,O2=1 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-noprune-unbox

$(bin)/malfunction-noprune-nounbox/%: FORCE | $(bin)/malfunction-noprune-nounbox/
	PRUNE_CONSTRUCTORS=0 UNBOX=0 OCAMLPARAM=_,O2=1 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-noprune-nounbox

$(bin)/malfunction-noinline/%: FORCE | $(bin)/malfunction-noinline/
	INLINE_AXIOMS=0 OCAMLPARAM=_,O2=1 make -C via_malfunction bin/$* TARGETDIR=../$(bin)/malfunction-noinline

$(results)/wide/:
	mkdir -p $@

bin/allbenches: $(foreach backend,$(backends),$(bin)/$(backend)/allbenches)

wide: FORCE bin/allbenches | $(results)/wide/
	taskset -c 3 hyperfine -N --warmup 2 -L bench "$(subst :,$(space),$(subst $(space),"$(comma)",$(benches)))" -L backend $(subst $(space),$(comma),$(backends)) "bin/{backend}/{bench}" --export-json $(results)/wide/$(shell date +"%Y-%m-%dT%T").json

$(bin)/%/:
	mkdir -p $@

.PHONY: Makefile clean wide bin/allbenches

clean:
	rm -rf bin
	make -C via_lean clean
	make -C via_malfunction clean

.NOTINTERMEDIATE:
