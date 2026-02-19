build:=build
bin:=bin

default:
	$(error No target specified)

benches:=
define register_test
$(let testname harness rest,$(subst :, ,$(1)),\
$(build)/$(testname)/Main.lean: $(harness).lean.template | $(build)/$(testname)/
	sed "s/{{testfunction}}/$(testname)/g" $(harness).lean.template > $$@
ifeq ($(harness),natio)
benches+=$(testname)
endif
)
endef

$(foreach testspec,$(shell cat ../TESTS),$(eval $(call register_test,$(testspec))))

$(build)/%/:
	mkdir -p $@

$(bin)/:
	mkdir -p $@

results:
	mkdir -p $@

$(build)/%/lean-toolchain: lean-toolchain.template | $(build)/%/
	cp $< $@

$(build)/%/lakefile.toml: lakefile.toml.template | $(build)/%/
	cp $< $@

bin/allbenches: $(foreach bench,$(benches),$(bin)/$(bench))

$(bin)/%: $(build)/%/Main.lean $(build)/%/lean-toolchain $(build)/%/lakefile.toml ../FromLeanCommon.lean ../FromLeanCommon | $(bin)/
	(cd $(build)/$* && lake build test)
	ln -srf $(build)/$*/.lake/build/bin/test $@
ifdef TARGETDIR
	ln -srf $@ $(TARGETDIR)/$*
endif

FORCE:

clean:
	rm -rf build bin

.PHONY: Makefile clean

.NOTINTERMEDIATE:
