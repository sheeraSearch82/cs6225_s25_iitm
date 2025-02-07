.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset05Sig.v
	$(COQC) Pset05.v

clean:
	rm -f *.vo* .*.aux *.cache *.glob
