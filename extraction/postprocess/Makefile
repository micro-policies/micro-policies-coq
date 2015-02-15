dist/build/postprocess/postprocess: Setup.hs src/Postprocess/Util/Tuple.hs src/Postprocess/Util/Monoid.hs src/Postprocess/Util/List.hs src/Postprocess/Util/Text.hs src/Postprocess/Util/Haskell.hs src/Postprocess/Processor.hs src/Postprocess/FileStructure.hs src/Postprocess/Imports.hs src/Postprocess/Constraints.hs src/Postprocess/Clean.hs src/Postprocess.hs src/Main.hs
	cabal configure
	cabal install --only-dependencies
	cabal	build

clean:
	cabal clean
