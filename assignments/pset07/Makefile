.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset07Sig.v
	$(COQC) Pset07.v
	$(COQC) Pset07Check.v

clean:
	rm -f *.vo* *.glob \#* *~
