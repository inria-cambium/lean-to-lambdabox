lean_build_id:=TODO

build:=build/$(lean_build_id)
bin:=bin/$(lean_build_id)

default:
	$(error No target specified)

define register_test
$(let testname harness rest,$(subst :, ,$(1)),\
$(build)/$(testname)/Main.lean: $(harness).lean.template | $(build)/$(testname)/
	sed "s/{{testfunction}}/$(testname)/g" $(harness).lean.template > $$@
)
endef

$(foreach testspec,$(shell cat ../TESTS),$(eval $(call register_test,$(testspec))))

$(build)/%/:
	mkdir -p $@

$(bin)/:
	mkdir -p $@

bin/:
	mkdir -p $@

results:
	mkdir -p $@

$(build)/%/lean-toolchain: lean-toolchain.template | $(build)/%/
	cp $< $@

$(build)/%/lakefile.toml: lakefile.toml.template | $(build)/%/
	cp $< $@

$(bin)/%: $(build)/%/Main.lean $(build)/%/lean-toolchain $(build)/%/lakefile.toml ../FromLeanCommon.lean ../FromLeanCommon | $(bin)/
	(cd $(build)/$* && lake build test)
	ln -srf $(build)/$*/.lake/build/bin/test $@

FORCE:

bin/%: $(bin)/% $(if $(TARGET),FORCE) | bin/
ifdef TARGET
	ln -srf $< $(TARGET)
else
	ln -srf $< $@
endif

#results/%.json: bin/% | results
#	taskset -c 3 hyperfine -N --export-json $@ $^

clean:
	rm -rf build bin

.PHONY: Makefile clean

.NOTINTERMEDIATE:
