.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile.source
	coq_makefile -f Makefile.source -o Makefile.coq

clean:
	rm -f */*.vo */*.v.d */*.glob */*~ */.#* Makefile.coq
	rm -f */*/*.vo */*/*.v.d */*/*.glob
	rm -rf os/extracted

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

REGEXP="s/([[:digit:]]+) ([[:digit:]]+)/scale=1; x=\(\1+\2\)\/1000; if(x<1) print 0; x/p"
PROCESS=grep total | tr -s ' ' | cut -d ' ' -f 2-3 | sed -rn $(REGEXP) | bc | tr -d '\n'

bc:
	@echo -n -e "%The shared/common/framework part\n\\\\newcommand{\\SHARED}{"
	@coqwc $(SHARED) | $(PROCESS)
	@echo -n -e "}\n%The policy-specific parts\n\\\\newcommand{\\SPECIF}{"
	@coqwc $(SPECIF) | $(PROCESS)
	@echo -n -e "}\n%The total\n\\\\newcommand{\\TOTAL}{"
	@coqwc $(SHARED) $(SPECIF) | $(PROCESS)
	@echo "}"

	@echo "%%%%%%%%%%%%%%%%%%%%%%%%%%%"
	@echo -n -e "%Generic libraries\n\\\\newcommand{\\LIB}{"
	@coqwc $(LIB) | $(PROCESS)
	@echo -n -e "}\n%Shared syntax and lemma used by all machines\n\\\\newcommand{\\COMMON}{"
	@coqwc $(COMMON) | $(PROCESS)
	@echo -n -e "}\n%Concrete machine\n\\\\newcommand{\\CONCRETE}{"
	@coqwc $(CONCRETE) | $(PROCESS)
	@echo -n -e "}\n%Everything else (symbolic dir)\n\\\\newcommand{\\SYMBOLIC}{"
	@coqwc $(SYMBOLIC) | $(PROCESS)
	@echo "}"

	@echo "%%%%%%%%%%%%%%%%%%%%%%%%%%%"
	@echo -n -e "%Memory safety\n\\\\newcommand{\\MEMSAFE}{"
	@coqwc $(MEMSAFE) | $(PROCESS)
	@echo -n -e "}\n%Dynamic sealing\n\\\\newcommand{\\SEALING}{"
	@coqwc $(SEALING) | $(PROCESS)
	@echo -n -e "}\n%Compartmentalization\n\\\\newcommand{\\COMPART}{"
	@coqwc $(COMPART) | $(PROCESS)
	@echo -n -e "}\n%Control Flow Integrity\n\\\\newcommand{\\CFI}{"
	@coqwc $(CFI) | $(PROCESS)
	@echo "}"

	@echo "%%%%%%%%%%%%%%%%%%%%%%%%%%%"
	@echo -n -e "%The symbolic machine definition\n\\\\newcommand{\\SYMDEF}{"
	@coqwc $(SYM_DEF) | $(PROCESS)
	@echo -n -e "}\n%The symbolic-concrete refinement proof\n\\\\newcommand{\\SYMCONPROOF}{"
	@coqwc $(SYM_CON_PROOF) | $(PROCESS)
	@echo -n -e "}\n%The generic fault handler (or something like that)\n\\\\newcommand{\\HANDLER}{"
	@coqwc $(HANDLER) | $(PROCESS)
	@echo "}"

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

# The target `extract-DIR' extracts the Coq code in `DIR' to Haskell code in
# `DIR/extracted/', using the file `DIR/extraction.v' and any extra code in
# `DIR/extra'.  The `DIR/extracted.v' file should probably just imports
# `extraction/extraction.v' and another library `LIB', and then `Recursive
# Extraction Library LIB'.  Don't pass `extract-DIR' `DIR's that are nested
# (i.e., that aren't exactly one level deep) or that contain "weird" characters
# (things that would break a regular expression, or an `@').
#
# This can also be made available from those subdirectories where one wants to
# extract, which is probably a good idea.
#
# Here's what `extract-DIR' does:
#   1. Makes sure the postprocessor exists.
#   2. Wipes out any past results of compiling the extraction file, letting us
#      use `make' in step 3.
#   3. Uses the Coq makefile to print out the Coq compilation command, then
#      fix it up so that:
#        (a) The references to `.' for the root directory become `..'.
#        (b) The references to `DIR/' (as in `DIR/extraction.vo') become `./'.
#      The result is stored in $(TEMP).
#   4. Runs the command from step 3 inside the directory DIR, deleting $(TEMP)
#      if it failed.
#   5. Delete $(TEMP) and the results of compiling the extraction file.
#   6. Postprocesses the extracted files into an `extracted' subdirectory of
#      `DIR', using extra code from an `extra' subdirectory.
extract-%: TEMP:=$(shell mktemp -t extraction)
extract-%: coq
	$(MAKE) -C extraction/postprocess
	rm -f $*/extraction.vo $*/extraction.glob
	$(MAKE) -nf Makefile.coq $*/extraction.vo \
	  | sed -r 's/ \. / .. /; s@'$*'/@./@'    \
	  > $(TEMP)
	  @ # This sed script fixes the `coqc' command to work from inside the given
	  @ # directory: `.' (the root) becomes `..', and `dir/' becomes './'.
	cd $* && $(SHELL) $(TEMP) || rm -f $(TEMP)
	rm -f $(TEMP) $*/extraction.vo $*/extraction.glob
	extraction/postprocess/postprocess $* $*/extracted $*/extra
