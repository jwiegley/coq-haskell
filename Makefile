MODULES_NODOC := CpdtTactics
MODULES_PROSE := Intro
MODULES_CODE  := Category
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE) Conclusion
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
TEX           := $(MODULES:%=%.v.tex)

VFILES = $(wildcard src/*.v)				\
         $(wildcard src/Control/*.v)			\
         $(wildcard src/Control/Monad/*.v)		\
         $(wildcard src/Control/Monad/Trans/*.v)	\
         $(wildcard src/Data/*.v)			\
         $(wildcard src/Data/Functor/*.v)		\
         $(wildcard src/Data/List/*.v)

VOFILES = $(patsubst %.v,%.vo,$(VFILES))

COQFLAGS = ""

MISSING = find src -name '*.v'						\
		 \(							\
		    ! -name Notes.v					\
		    ! -name CpdtTactics.v				\
		    ! -name Extract.v					\
		    -print						\
		 \) |							\
		 xargs egrep -i -Hn '(abort|admit|undefined)'     |	\
		       egrep -v 'Definition undefined'

#     extract/Hask/Choice.hs			\
#     extract/Hask/Ssreflect.hs			\

all: $(VOFILES) extract/Hask/Extract.hs		\
     extract/Hask/Eqtype.hs			\
     extract/Hask/Fintype.hs			\
     extract/Hask/Seq.hs			\
     extract/Hask/Ssrbool.hs			\
     extract/Hask/Ssrfun.hs			\
     extract/Hask/Ssrnat.hs
	$(MISSING) || exit 0

%.vo: %.v Makefile.coq
	@$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	@$(MAKE) extract/Hask/Extract.hs

Makefile.coq: _CoqProject
	@coq_makefile -f _CoqProject -o $@
	@perl -i fixmake.pl $@

extract/Hask:
	-mkdir -p extract/Hask

extract/Hask/Extract.hs: extract/Hask src/Extract.vo
	@perl -i fixcode.pl *.hs
	@ls -1 *.hs | egrep -v 'Setup.hs' | \
	    while read file; do mv $$file extract/Hask; done

# These rules are for case-sensitive filesystems
extract/Hask/Eqtype.hs: extract/Hask/eqtype.hs
	@mv $< $@

extract/Hask/Choice.hs: extract/Hask/choice.hs
	@mv $< $@

extract/Hask/Fintype.hs: extract/Hask/fintype.hs
	@mv $< $@

extract/Hask/Seq.hs: extract/Hask/seq.hs
	@mv $< $@

extract/Hask/Ssrbool.hs: extract/Hask/ssrbool.hs
	@mv $< $@

extract/Hask/Ssreflect.hs: extract/Hask/ssreflect.hs
	@mv $< $@

extract/Hask/Ssrfun.hs: extract/Hask/ssrfun.hs
	@mv $< $@

extract/Hask/Ssrnat.hs: extract/Hask/ssrnat.hs
	@mv $< $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ls -1 extract/Hask/* | egrep -v '(Utils).hs' | \
	    while read file; do rm -f $$file; done
	rm -f Makefile.coq Setup
	rm -fr dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo .*.aux
