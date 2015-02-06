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

LIB=lib/*.v
COMMON=common/*.v
CONCRETE=concrete/*.v
SYMBOLIC=symbolic/*.v
SHARED=$(LIB) $(COMMON) $(CONCRETE) $(SYMBOLIC)

MEMSAFE=memory_safety/*.v
SEALING=sealing/*.v
COMPART=compartmentalization/*.v
CFI    =cfi/*.v
SPECIF=$(MEMSAFE) $(SEALING) $(COMPART) $(CFI)

# Further breaking it down for symbolic dir
SYM_DEF=symbolic/symbolic.v symbolic/exec.v
SYM_CON_PROOF=symbolic/backward.v symbolic/forward.v symbolic/refinement_common.v
HANDLER=symbolic/rules.v symbolic/fault_handler.v symbolic/int_32.v

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

bc-shared:
	@echo "Generic libraries"
	@echo "     spec    proof comments"
	@coqwc $(LIB) | grep total
	@echo "Shared syntax and lemma used by all machines"
	@echo "     spec    proof comments"
	@coqwc $(COMMON) | grep total
	@echo "Concrete machine"
	@echo "     spec    proof comments"
	@coqwc $(CONCRETE) | grep total
	@echo "Everything else (symbolic dir)"
	@echo "     spec    proof comments"
	@coqwc $(SYMBOLIC) | grep total

bc-specif:
	@echo "Memory safety"
	@echo "     spec    proof comments"
	@coqwc $(MEMSAFE) | grep total
	@echo "Dynamic sealing"
	@echo "     spec    proof comments"
	@coqwc $(SEALING) | grep total
	@echo "Compartmentalization"
	@echo "     spec    proof comments"
	@coqwc $(COMPART) | grep total
	@echo "Control Flow Integrity"
	@echo "     spec    proof comments"
	@coqwc $(CFI) | grep total

bc-sym:
	@echo "The symbolic machine definition"
	@coqwc $(SYM_DEF) | grep total
	@echo "The symbolic-concrete refinement proof"
	@coqwc $(SYM_CON_PROOF) | grep total
	@echo "The generic fault handler (or something like that)"
	@coqwc $(HANDLER) | grep total

EXCLUDE=--exclude=testing --exclude=.gitignore --exclude=compartmentalization/global-hint.el

dist: clean
	rm -f rm ../micropolicies.tar.gz
	tar czvf ../micropolicies.tar.gz . --transform 's/^\./micropolicies/' $(EXCLUDE)

DIR=../micropolicies-coq-anon
COQ_UTILS=../coq-utils

dist-anon: clean
	rm -dfr rm $(DIR) ../micropolicies-coq-anon.tar.gz
	cp -R . $(DIR)
	rm -dfr $(DIR)/.git
	cd $(COQ_UTILS); make clean
	cp -R $(COQ_UTILS) $(DIR)
	rm -dfr $(DIR)/coq-utils/.git
	perl -0777 -i -pe 's/Copyright.*Permission/Copyright Anonymized\n\nPermission/igs' $(DIR)/coq-utils/LICENSE
	perl -0777 -i -pe 's/Copyright.*Permission/Copyright Anonymized\n\nPermission/igs' $(DIR)/LICENSE
	perl -0777 -i -pe 's/Description.*Prerequisites/Prerequisites/igs' $(DIR)/README.md
	perl -0777 -i -pe 's/The CoqUtils library \(https.*coq-utils\)/The CoqUtils library \(included in coq-utils subdir\)/igs' $(DIR)/README.md
        # Next command doesn't work for nested comments, please don't add any
	find $(DIR) -name '*.v' -exec perl -0777 -i -pe 's/\(\*.*?\*\)//igs' {} \;
	cd $(DIR); tar czvf ../micropolicies-coq-anon.tar.gz . --transform 's/^\./micropolicies-coq-anon/' $(EXCLUDE)

coqide:
	coqide -R . MicroPolicies
