MODULES_NODOC := CpdtTactics
MODULES_PROSE := Intro
MODULES_CODE  := Category
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE) Conclusion
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
TEX           := $(MODULES:%=%.v.tex)

VFILES = $(wildcard src/*.v)
VOFILES = $(patsubst %.v,%.vo,$(VFILES))

COQFLAGS = ""

MISSING = find src -name '*.v'						\
		 \(							\
		    ! -name Notes.v					\
		    ! -name CpdtTactics.v				\
		    -print						\
		 \) |							\
		 xargs egrep -i -Hn '(abort|admit|undefined)'     |	\
		       egrep -v 'Definition undefined'

all: $(VOFILES) extracted/Hask/Main.hs		\
     extracted/Hask/Eqtype.hs			\
     extracted/Hask/Choice.hs			\
     extracted/Hask/Fintype.hs			\
     extracted/Hask/Seq.hs			\
     extracted/Hask/Ssrbool.hs			\
     extracted/Hask/Ssreflect.hs		\
     extracted/Hask/Ssrfun.hs			\
     extracted/Hask/Ssrnat.hs
	$(MISSING) || exit 0

%.vo: %.v Makefile.coq
	@$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	@$(MAKE) extracted/Hask/Main.hs

Makefile.coq: _CoqProject
	@coq_makefile -f _CoqProject -o $@
	@perl -i fixmake.pl $@

extracted/Hask/Main.hs: src/Main.vo
	@ls -1 *.hs | egrep -v 'Setup.hs' | \
	    while read file; do mv $$file extracted/Hask; done
	@perl -i fixcode.pl extracted/Hask/*.hs

# These rules are for case-sensitive filesystems
extracted/Hask/Eqtype.hs: extracted/Hask/eqtype.hs
	@mv $< $@

extracted/Hask/Choice.hs: extracted/Hask/choice.hs
	@mv $< $@

extracted/Hask/Fintype.hs: extracted/Hask/fintype.hs
	@mv $< $@

extracted/Hask/Seq.hs: extracted/Hask/seq.hs
	@mv $< $@

extracted/Hask/Ssrbool.hs: extracted/Hask/ssrbool.hs
	@mv $< $@

extracted/Hask/Ssreflect.hs: extracted/Hask/ssreflect.hs
	@mv $< $@

extracted/Hask/Ssrfun.hs: extracted/Hask/ssrfun.hs
	@mv $< $@

extracted/Hask/Ssrnat.hs: extracted/Hask/ssrnat.hs
	@mv $< $@

clean:
	rm -f *.d *.vo *.glob Makefile.coq .*.aux
	rm -fr .coq-native

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ls -1 extracted/Hask/* | egrep -v '(Utils).hs' | \
	    while read file; do rm -f $$file; done
	rm -f Makefile.coq Setup
	rm -fr dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo
