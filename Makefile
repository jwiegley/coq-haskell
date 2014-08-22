MODULES_NODOC := CpdtTactics
MODULES_PROSE := Intro
MODULES_CODE  := Category
MODULES_DOC   := $(MODULES_PROSE) $(MODULES_CODE) Conclusion
MODULES       := $(MODULES_NODOC) $(MODULES_DOC)
TEX           := $(MODULES:%=%.v.tex)

COQFLAGS = ""

MISSING = find . -name '*.v' ! -name Notes.v ! -name CpdtTactics.v |	\
		xargs egrep -i -Hn '(admit|abort)'

all: Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)
	$(MISSING) || exit 0

Makefile.coq: *.v
	coq_makefile -f _CoqProject > Makefile.coq
	sed -i -e 's#cd "./." && .(MAKE) all#cd ./. ; echo $(MAKE) all#' Makefile.coq

clean:
	rm -f *.d *.vo *.glob Makefile.coq .*.aux
	rm -fr .coq-native
