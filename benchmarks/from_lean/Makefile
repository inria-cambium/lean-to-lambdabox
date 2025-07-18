build_id:=TODO

bin:=bin/$(build_id)

default:
	$(error No target specified)

FORCE:

$(bin)/malflambda-O2/%: FORCE | $(bin)/malflambda-O2/
	FLAMBDA=1 OCAMLPARAM=_,O2=1 make -C via_malfunction bin/$* TARGET=../$@

$(bin)/malflambda-O3/%: FORCE | $(bin)/malflambda-O3/
	FLAMBDA=1 OCAMLPARAM=_,O3=1 make -C via_malfunction bin/$* TARGET=../$@

$(bin)/malfunction-noflambda/%: FORCE | $(bin)/malfunction-noflambda/
	FLAMBDA=0 make -C via_malfunction bin/$* TARGET=../$@

$(bin)/lean-compilernew/%: FORCE | $(bin)/lean-compilernew/
	make -C via_lean bin/$* TARGET=../$@

bin/%: $(bin)/%
	mkdir -p $(dir $@)
	ln -srf $< $@

$(bin)/%/:
	mkdir -p $@

.PHONY: Makefile clean

clean:
	rm -rf bin
	make -C via_lean clean
	make -C via_malfunction clean

.NOTINTERMEDIATE:
