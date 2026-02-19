PEREGRINE_SWITCH?=peregrine
MALFUNCTION_NO_FLAMBDA_SWITCH?=malfunction
MALFUNCTION_FLAMBDA_SWITCH?=malfunction+flambda

# 0 to make without flambda, 1 to use flambda; default is 1.
FLAMBDA?=1
ifeq ($(FLAMBDA),1)
MALFUNCTION_SWITCH=$(MALFUNCTION_FLAMBDA_SWITCH)
else ifeq ($(FLAMBDA),0)
MALFUNCTION_SWITCH=$(MALFUNCTION_NO_FLAMBDA_SWITCH)
else
$(error Variable FLAMBDA must be either 0 or 1, is $(FLAMBDA))
endif

# 0 to use "regular" axioms, 1 to use inlined axioms; default is 1.
INLINE_AXIOMS?=1
ifeq ($(INLINE_AXIOMS),1)
DECIDABLEML=decidable-inline.ml
EQML=eq-inline.ml
NATML=nat-inline.ml
INTML=int-inline.ml
else ifeq ($(INLINE_AXIOMS),0)
DECIDABLEML=decidable.ml
EQML=eq.ml
NATML=nat.ml
INTML=int.ml
else
$(error Variable INLINE_AXIOMS must be either 0 or 1, is $(INLINE_AXIOMS))
endif

# 0 to keep all constructor arguments, 1 to remove irrelevant ones; default is 1.
PRUNE_CONSTRUCTORS?=1
ifeq ($(PRUNE_CONSTRUCTORS),1)
DECIDABLEML=decidable-pruned.ml
ERASURE_CONFIG+=remove_irrel_constr_args := true,
else ifeq ($(PRUNE_CONSTRUCTORS),0)
else
$(error Variable PRUNE_CONSTRUCTORS must be either 0 or 1, is $(PRUNE_CONSTRUCTORS))
endif

# 0 to keep values of one-constructor one-field inductive types boxed, 1 to unbox; default is 1.
BETARED?=1
UNBOX?=1
ifeq ($(BETARED),0)
PEREGRINE_CONFIG=no_betared.config
else ifeq ($(UNBOX),1)
PEREGRINE_CONFIG=unbox.config
else ifeq ($(UNBOX),0)
PEREGRINE_CONFIG=no_unbox.config
else
$(error Variable UNBOX must be either 0 or 1, is $(UNBOX))
endif

ARRAYML?=JCFArray.ml
ifeq ($(ARRAYML),SekArray.ml)
OCAMLPACKAGE=zarith,sek
else
OCAMLPACKAGE=zarith
endif

PEREGRINE=opam exec --switch=$(PEREGRINE_SWITCH) -- peregrine
MALFUNCTION=opam exec --switch=$(MALFUNCTION_SWITCH) -- malfunction
OCAMLOPT=opam exec --switch=$(MALFUNCTION_SWITCH) -- ocamlfind ocamlopt -package $(OCAMLPACKAGE)

INLINING?=1

# Space-separated.
malfunction_build_info:=OCAML_ARGS=$(OCAML_ARGS)\
FLAMBDA=$(FLAMBDA)\
INLINE_AXIOMS=$(INLINE_AXIOMS)\
PRUNE_CONSTRUCTORS=$(PRUNE_CONSTRUCTORS)\
UNBOX=$(UNBOX)\
ERASURE_CONFIG=$(ERASURE_CONFIG)\
PEREGRINE_SWITCH=$(PEREGRINE_SWITCH)\
MALFUNCTION_SWITCH=$(MALFUNCTION_SWITCH)\
MALFUNCTION_ARGS=$(MALFUNCTION_ARGS)\
OCAMLPARAM=$(OCAMLPARAM)\
OCAMLPACKAGE=$(OCAMLPACKAGE)\
DECIDABLEML=$(DECIDABLEML)\
EQML=$(EQML)\
NATML=$(NATML)\
INTML=$(INTML)\
ARRAYML=$(ARRAYML)\
INLINING=$(INLINING)\
BETARED=$(BETARED)

malfunction_build_id:= $(shell echo "$(malfunction_build_info)" | sha256sum | head -c 8)

build:=build/$(malfunction_build_id)
bin:=bin/$(malfunction_build_id)

benches:=
define register_test
$(let testname harness rest,$(subst :, ,$(1)),\

# The shell magic capitalizes the first letter of the test name to make a module name.
$(build)/$(testname)_main.ml: $(harness).ml.template | $(build)
	sed "s/{{testmodule}}/$(shell echo $(testname) | sed 's/^./\U&/')/g" $(harness).ml.template > $$@
ifeq ($(harness),natio)
benches+=$(testname)
endif
)
endef

$(foreach testspec,$(shell cat ../TESTS),$(eval $(call register_test,$(testspec))))

FORCE:

bin/%: $(bin)/% $(if $(TARGETDIR),FORCE)
ifdef TARGETDIR
	ln -srf $< $(TARGETDIR)/$*
else
	ln -srf $< $@
endif

bin/allbenches: $(foreach bench,$(benches),bin/$(bench))

$(bin)/%: $(build)/decidable.cmx\
	  $(build)/eq.cmx\
          $(build)/nat.cmx\
          $(build)/int.cmx\
	  $(build)/LeanArray.cmx\
          $(build)/axioms.cmx\
	  $(build)/%.cmx\
          $(build)/%_main.ml | $(bin)
	$(OCAMLOPT) -I $(build) -linkpkg $(OCAML_ARGS) $^ -o $@

default:
	$(error No target specified)

$(build):
	mkdir -p $@
	printf "%s\\n" $(malfunction_build_info) > $(build)/cfg
$(bin):
	mkdir -p $@

$(build)/axioms.mli: axioms.mli | $(build)
	cp $< $@

$(build)/axioms.ml: axioms.ml | $(build)
	cp $< $@

$(build)/decidable.mli: decidable.mli | $(build)
	cp $< $@

$(build)/decidable.ml: $(DECIDABLEML) | $(build)
	cp $< $@

# decidable.cmi handled by generic rule (no prerequisites)

$(build)/decidable.cmx: $(build)/decidable.ml $(build)/decidable.cmi
	$(OCAMLOPT) -I $(build) -c $<

$(build)/eq.mli: eq.mli | $(build)
	cp $< $@

$(build)/eq.ml: $(EQML) | $(build)
	cp $< $@

# eq.cmi handled by generic rule (no prerequisites)

$(build)/eq.cmx: $(build)/eq.ml $(build)/eq.cmi
	$(OCAMLOPT) -I $(build) -c $<

$(build)/LeanArray.mli: LeanArray.mli | $(build)
	cp $< $@

$(build)/LeanArray.ml: $(ARRAYML) | $(build)
	cp $< $@

# LeanArray.cmi handled by generic rule (no prerequisites)

$(build)/LeanArray.cmx: $(build)/LeanArray.ml $(build)/LeanArray.cmi
	$(OCAMLOPT) -I $(build) -c $<

$(build)/nat.mli: nat.mli | $(build)
	cp $< $@

$(build)/nat.ml: $(NATML) | $(build)
	cp $< $@

$(build)/nat.cmi: $(build)/nat.mli $(build)/decidable.cmi
	$(OCAMLOPT) -I $(build) -c $<

$(build)/nat.cmx: $(build)/nat.ml $(build)/nat.cmi $(build)/decidable.cmx
	$(OCAMLOPT) -I $(build) -c $<

$(build)/int.mli: int.mli | $(build)
	cp $< $@

$(build)/int.ml: $(INTML) | $(build)
	cp $< $@

$(build)/int.cmi: $(build)/int.mli $(build)/decidable.cmi
	$(OCAMLOPT) -I $(build) -c $<

$(build)/int.cmx: $(build)/int.ml $(build)/int.cmi $(build)/decidable.cmx
	$(OCAMLOPT) -I $(build) -c $<

$(build)/axioms.cmi: $(build)/axioms.mli $(build)/decidable.cmi $(build)/nat.cmi $(build)/int.cmi $(build)/eq.cmi $(build)/LeanArray.cmi
	$(OCAMLOPT) -I $(build) -c $<

$(build)/axioms.cmx: $(build)/axioms.ml $(build)/axioms.cmi $(build)/nat.cmx $(build)/int.cmx $(build)/eq.cmx
	$(OCAMLOPT) -I $(build) -c $<

$(build)/%.lean: test.lean.template | $(build)
	sed "s/{{testfunction}}/$*/g; s/{{extractiondir}}/$(subst /,\/,$(build))/g; s/{{erasureconfig}}/$(ERASURE_CONFIG)/g" $< > $@

# The .ast file containing λbox S-expressions and the .mli file containing the signature
# of the exposed main function are generated by elaborating the appropriate .lean file.
# Running `lake build` would not work as lake would do nothing on subsequent runs if the .lean has not changed.
$(build)/%.ast $(build)/%.mli: $(build)/%.lean ../FromLeanCommon.lean ../FromLeanCommon/
	lake lean $<

ifeq ($(INLINING),1)
$(build)/%.mlf: $(build)/%.ast
	$(PEREGRINE) compile $< $(PEREGRINE_CONFIG) --attributes=$<.inlinings > /dev/null
else
$(build)/%.mlf: $(build)/%.ast
	$(PEREGRINE) compile $< $(PEREGRINE_CONFIG) > /dev/null
endif

# Malfunction will silently generate an empty .cmi file if not given an .mli interface, but that won't work for linking later.
$(build)/%.cmi: $(build)/%.mli
	$(OCAMLOPT) -c $<

# Depend on axioms.cmx in order to allow cross-module optimizations (esp. inlining)
$(build)/%.cmx: $(build)/%.mlf $(build)/%.cmi $(build)/axioms.cmx
	cd $(build) && $(MALFUNCTION) cmx $(MALFUNCTION_ARGS) $*.mlf

clean:
	rm -rf build bin

.PHONY: Makefile clean

# Don't consider anything as an intermediate file.
.NOTINTERMEDIATE:
