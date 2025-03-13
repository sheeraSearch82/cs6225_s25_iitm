.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset09Sig.v
	$(COQC) Pset09.v

clean:
	rm -f *.vo *.glob *.aux .*.aux .lia.cache .nia.cache *.vok *.vos
