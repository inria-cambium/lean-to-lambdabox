build_id:=TODO

bin:=bin/$(build_id)

FORCE:

$(bin)/malfunction-flambda/%: FORCE
	FLAMBDA=1 make -C via_malfunction bin/$* TARGET=../$@

$(bin)/malfunction-noflambda/%: FORCE
	FLAMBDA=1 make -C via_malfunction bin/$* TARGET=../$@

bin/%: $(bin)/%
	ln -srf $< $@

define register_test
$(let testname harness rest,$(subst :, ,$(1)),\
phonytargets+=bin/malfunction-flambda/$(testname)
phonytargets+=bin/malfunction-noflambda/$(testname)
)
endef

$(foreach testspec,$(shell cat TESTS),$(eval $(call register_test,$(testspec))))

.PHONY: $(phonytargets)

default:
	@echo $(OUT)
