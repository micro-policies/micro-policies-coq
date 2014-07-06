.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile.source
	coq_makefile -f Makefile.source -o Makefile.coq

clean:
	rm -f */*.vo */*.v.d */*.glob */*~ */.#* Makefile.coq

test: coq
	$(MAKE) -C sealing runtest

SHARED=lib/ordered.v lib/partial_maps.v lib/utils.v common/*.v concrete/*.v symbolic/*.v

SPECIF=memory_safety/*.v sealing/*.v sfi/*.v cfi/*.v

# TODO: should move reusable parts out of sfi and add to SHARED above

# There are 2 files excluded from build in symbolic (initial.v and testing.v)
# Q: What should we do about them? Can we bring them back?

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
	tar czvf ../micropolicies.tar.gz . --transform 's/^\./micropolicies/' --exclude=notes --exclude=old --exclude=testing --exclude=.gitignore --exclude=cfi/review.org --exclude=sfi/global-hint.el
