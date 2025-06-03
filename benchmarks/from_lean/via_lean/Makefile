default:
	@echo "No target specified."

build/%/:
	mkdir -p $@

bin:
	mkdir -p $@

results:
	mkdir -p $@

build/%/lean-toolchain: lean-toolchain.template | build/%/
	cp lean-toolchain.template $@

build/%/lakefile.toml: lakefile.toml.template | build/%/
	cp lakefile.toml.template $@

build/%_runonce/Main.lean: runonce.lean.template ../FromLeanCommon.lean | build/%_runonce/
	sed "s/{{testfunction}}/$*/g" runonce.lean.template > $@

build/%_repeat/Main.lean: repeat.lean.template ../FromLeanCommon.lean | build/%_repeat/
	sed "s/{{testfunction}}/$*/g" repeat.lean.template > $@

bin/%: build/%/Main.lean build/%/lean-toolchain build/%/lakefile.toml | bin
	(cd build/$* && lake build test)
	cp build/$*/.lake/build/bin/test $@

results/%.json: bin/% | results
	taskset -c 3 hyperfine -N --export-json $@ $^

clean:
	rm -rf build bin

.PHONY: clean

# Don't delete intermediate files.
.SECONDARY:
