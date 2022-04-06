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

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean

fullclean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean fullclean force
