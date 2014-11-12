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

SPECIF=memory_safety/*.v sealing/*.v compartmentalization/*.v cfi/*.v

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

DIR=../micropolicies-coq-anon

dist-anon: clean
	rm -dfr rm $(DIR) ../micropolicies-coq-anon.tar.gz
	cp -R . $(DIR)
	rm -dfr $(DIR)/.git
	perl -0777 -i -pe 's/Copyright.*Permission/Copyright Anonymized\n\nPermission/igs' $(DIR)/LICENSE
	perl -0777 -i -pe 's/Description.*Prerequisites/Prerequisites/igs' $(DIR)/README.md
        # Next command doesn't work for nested comments, please don't add any until Saturday
	find $(DIR) -name '*.v' -exec perl -0777 -i -pe 's/\(\*.*?\*\)//igs' {} \;
	cd $(DIR); tar czvf ../micropolicies-coq-anon.tar.gz . --transform 's/^\./micropolicies-coq-anon/' --exclude=testing --exclude=.gitignore --exclude=cfi/review.org --exclude=compartmentalization/global-hint.el

coqide:
	coqide -R . MicroPolicies
