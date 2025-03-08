.PHONY: coq clean

COQC=coqc -q -R ../../frap Frap -R . ""

coq:
	$(COQC) Pset03Signature.v
	$(COQC) Pset03Implementation.v

clean:
	rm -f *.vo* *.glob .*.aux
