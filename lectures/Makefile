all: Makefile.coq
	$(MAKE) -f Makefile.coq

html:
	coqdoc FunctionalProgramming.v
	coqdoc Logic.v
	coqdoc Induction.v

Makefile.coq: Makefile _CoqProject *.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	rm -f *~ *.glob *.vo* *.html *.css

distclean: clean
	rm -f Makefile.coq
	rm -f Makefile.coq.conf
