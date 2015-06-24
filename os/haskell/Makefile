all:
	ghc -i../extracted \
	    -Wall -fno-warn-name-shadowing \
	    -j \
	    -odir compiled -hidir compiled \
	    $$(find . -type f -name '*.hs')
# Can't specify -O2, or I get a "ghc: panic! (the 'impossible' happened)".  It's
# probably for the best, given the crazy `unsafePerformIO` shenanigans the
# extracted code does with `()` (and not `Any`, grr).

clean:
	-rm -rf compiled
