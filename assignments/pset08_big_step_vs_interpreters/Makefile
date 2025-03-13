.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset08Sig.v
	$(COQC) Pset08.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .*.cache *.vok *.vos
