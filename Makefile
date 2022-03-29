COQFLAGS = ""
MISSING  =								\
	find . -name '*.v' ! -name Notes.v				\
		! -name Extract.v					\
		! -name CpdtTactics.v					\
                ! -name '*2.v'                                   |	\
		xargs egrep -i -Hn '(abort|admit|undefined)'     |	\
		      egrep -v 'Definition undefined'            |	\
		      egrep -v '(old|new|research)/'

VFILES = $(wildcard src/*.v)
VOFILES = $(patsubst %.v,%.vo,$(VFILES))

all: $(VOFILES) extract/Hask/Prelude0.hs
	-@$(MISSING) || exit 0

%.vo: %.v Makefile.coq
	$(MAKE) -f Makefile.coq -j10 -k OPT=$(COQFLAGS)
	@$(MAKE) extract/Hask/Prelude0.hs

extract/Hask/Prelude0.hs: src/Prelude.vo
	@if [ ! -d extract ]; then rm -f extract; fi
	@if [ ! -d extract ]; then mkdir extract; fi
	@ls -1 *.hs | egrep -v '(Setup|Hask).hs' |		\
	    while read file; do					\
              if ! grep "module Hask" $$file; then		\
	        perl -i fixcode.pl $$file;			\
              fi;						\
	      if [ "$$file" = "eqtype.hs" ]; then		\
                mv eqtype.hs extract/Hask/Eqtype.hs;		\
	      elif [ "$$file" = "choice.hs" ]; then		\
                mv choice.hs extract/Hask/Choice.hs;		\
	      elif [ "$$file" = "fintype.hs" ]; then		\
                mv fintype.hs extract/Hask/Fintype.hs;		\
	      elif [ "$$file" = "seq.hs" ]; then		\
                mv seq.hs extract/Hask/Seq.hs;			\
	      elif [ "$$file" = "ssrbool.hs" ]; then		\
                mv ssrbool.hs extract/Hask/Ssrbool.hs;		\
	      elif [ "$$file" = "ssreflect.hs" ]; then		\
                mv ssreflect.hs extract/Hask/Ssreflect.hs;	\
	      elif [ "$$file" = "ssrfun.hs" ]; then		\
                mv ssrfun.hs extract/Hask/Ssrfun.hs;		\
	      elif [ "$$file" = "ssrnat.hs" ]; then		\
                mv ssrnat.hs extract/Hask/Ssrnat.hs;		\
              else						\
                mv $$file extract/Hask;				\
	      fi						\
            done

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

install: _CoqProject Makefile.coq
	make -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -fr Makefile.coq Setup extract/*
	rm -fr dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo
