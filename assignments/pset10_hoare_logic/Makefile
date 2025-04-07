.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset10Sig.v
	$(COQC) Pset10.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .*.cache *.vok *.vos
