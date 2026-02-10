all: theory
.PHONY: all

RocqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o RocqMakefile

RocqMakefile_: _CoqProject_
	rocq makefile -f _CoqProject_ -o RocqMakefile_

theory: RocqMakefile
	+@make -f RocqMakefile
.PHONY: theory

build-ci: RocqMakefile_
	+@make -f RocqMakefile_
.PHONY: build-ci

clean: RocqMakefile
	+@make -f RocqMakefile clean
	rm -f RocqMakefile
.PHONY: clean

clean-make:
	rm -f RocqMakefile
.PHONY: clean-make

install: RocqMakefile
	+@make -f RocqMakefile install
.PHONY: install

uninstall: RocqMakefile
	+@make -f RocqMakefile uninstall
.PHONY: uninstall
