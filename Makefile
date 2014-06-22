.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile.source
	coq_makefile -f Makefile.source -o Makefile.coq

clean:
	rm -f */*.vo */*.v.d */*.glob */*~ Makefile.coq temp temp.*

test: coq
	ocamlc temp.mli
	sed -i -e 's/Coq__2\.tag/tag/g' temp.ml
	sed -i -e 's/let tag = tag/let tag \= Coq\_\_2\.tag/g' temp.ml
	ocamlc temp.ml -o temp
	./temp
