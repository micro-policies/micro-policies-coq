.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile.source
	coq_makefile -f Makefile.source -o Makefile.coq

clean:
	rm -f */*.vo */*.v.d */*.glob */*~ */.#* Makefile.coq
	rm -f */*/*.vo */*/*.v.d */*/*.glob

test: coq
	$(MAKE) -C sealing runtest

SHARED=lib/*.v common/*.v concrete/*.v symbolic/*.v

SPECIF=memory_safety/*.v sealing/*.v compartmentalization/*.v cfi/*.v trivial/*.v

bc:
	@echo "The shared/common/framework part"
	@echo "     spec    proof comments"
	@coqwc $(SHARED) | grep total
	@echo "The policy-specific parts"
	@echo "     spec    proof comments"
	@coqwc $(SPECIF) | grep total
	@echo "The total"
	@echo "     spec    proof comments"
	@coqwc $(SHARED) $(SPECIF) | grep total

dist: clean
	rm -f rm ../micropolicies.tar.gz
	tar czvf ../micropolicies.tar.gz . --transform 's/^\./micropolicies/' --exclude=testing --exclude=.gitignore --exclude=cfi/review.org --exclude=compartmentalization/global-hint.el

coqide:
	coqide -R . MicroPolicies
