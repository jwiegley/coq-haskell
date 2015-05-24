MODULES_NODOC := CpdtTactics
MODULES_PROSE := Intro
MODULES_CODE  := Category
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE) Conclusion
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
TEX           := $(MODULES:%=%.v.tex)

VFILES = $(wildcard *.v)
VOFILES = $(patsubst %.v,%.vo,$(VFILES))

COQFLAGS = ""

MISSING = find . -name 'research' -prune -o				\
		 -name '*.v'						\
		 \(							\
		    ! -name Notes.v					\
		    ! -name CpdtTactics.v				\
		    -print						\
		 \) |							\
		 xargs egrep -i -Hn '(abort|admit|undefined)'     |	\
		       egrep -v 'Definition undefined'

all: Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	$(MISSING) || exit 0

%.vo: %.v Makefile.coq
	@$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	@$(MAKE) LinearScan/Main.hs

Makefile.coq: _CoqProject
	@coq_makefile -f _CoqProject -o $@
	@perl -i fixmake.pl $@

clean:
	rm -f *.d *.vo *.glob Makefile.coq .*.aux
	rm -fr .coq-native

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	ls -1 LinearScan/* | egrep -v '(Utils).hs' | \
	    while read file; do rm -f $$file; done
	rm -f Makefile.coq Setup
	rm -fr dist .coq-native
	rm -fr .hdevtools.sock *.glob *.d *.vo
