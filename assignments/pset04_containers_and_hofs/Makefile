.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset04Sig.v
	$(COQC) Pset04.v

clean:
	rm -f *.vo *.glob .*.aux *.aux .lia.cache .nia.cache *.vok *.vos
