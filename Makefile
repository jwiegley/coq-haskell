MISSING  =								\
	find . -name '*.v'						\
		! -name Notes.v						\
		! -name Extract.v					\
		! -name CpdtTactics.v					\
                ! -name '*2.v'                                    |	\
		xargs egrep -i -Hn '(Fail|abort|admit|undefined)' |	\
		      egrep -v 'Definition undefined'             |	\
		      egrep -v '(old|new|research)/'


all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all
	-@$(MISSING) || exit 0

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

install: Makefile.coq
	@+$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean
	rm -fr Setup extract dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo

fullclean: clean
	@+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf .Makefile.d

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force


extraction: src/Extract.vo
	@if [ ! -d extract ]; then rm -fr extract; fi
	@if [ ! -d extract ]; then mkdir -p extract/Hask; fi
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
