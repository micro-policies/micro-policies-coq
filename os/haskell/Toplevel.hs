{-# OPTIONS_GHC -fno-warn-unused-imports #-}
module Toplevel where

import qualified Action
import qualified Automorphism
import qualified Bigop
import qualified BinNat
import qualified BinNums
import qualified BinPos
import qualified Binomial
import qualified Bool
import qualified Choice
import qualified Common
import qualified Concrete
import qualified Datatypes
import qualified Div
import qualified Eqtype
import qualified Exec
import qualified Exec0
import qualified Fault_handler
import qualified Finalg
import qualified Finfun
import qualified Fingroup
import qualified Finset
import qualified Fintype
import qualified Fperm
import qualified Fset
import qualified Hseq
import qualified Int_0
import qualified Int_32
import qualified Intdiv
import qualified Isolate_sets
import qualified Logic
import qualified Matrix
import qualified Morphism
import qualified Mxalgebra
import qualified Nominal
import qualified Ord
import qualified Os
import qualified Partmap
import qualified Path
import qualified Peano
import qualified Perm
import qualified Poly
import qualified Polydiv
import qualified Prime
import qualified Quotient
import qualified Ranges
import qualified Rat
import qualified Refinement_common
import qualified Rules
import qualified Segment
import qualified Seq
import qualified Specif
import qualified Ssralg
import qualified Ssrbool
import qualified Ssreflect
import qualified Ssrfun
import qualified Ssrint
import qualified Ssrnat
import qualified Ssrnum
import qualified Symbolic
import qualified Symbolic0
import qualified Tuple
import qualified Types
import qualified Vector
import qualified Word
import qualified Zmodp

import Haskell.Util
import Haskell.ImplicitEffects
import Haskell.Pretty
import Haskell.Inspect
import Haskell.Types
import Haskell.Word
import Haskell.Machine
import Haskell.Assembler hiding
  ( nop, const_, mov, binop, load, store, jump, bnz, jal
  , jumpEpc, addRule, getTag, putTag, halt )
import Haskell.OS

import Control.Applicative
import Control.Monad
import Control.Lens

listing :: State -> [MWord] -> IO ()
listing = (print .) . inspectAddrs

aroundPC :: State -> Integer -> IO ()
aroundPC = (print .) . inspectAroundPC

regfile :: State -> IO ()
regfile = print . inspectRegFile

summarize :: State -> [MWord] -> Integer -> IO ()
summarize s as r = do putStrLn "Instructions:"
                      aroundPC s r
                      putStrLn ""
                      putStrLn "Registers:"
                      regfile s
                      unless (null as) $ do
                        putStrLn ""
                        putStrLn "Data:"
                        listing s as

runState :: SyscallAddresses -> State -> [MWord] -> Integer -> Integer -> IO ()
runState addrs s0 as r n = do
  let (i,s) = stepMany' addrs n s0
  putStrLn $ concat [ "Ran for ", show i, "/", show n
                    , " step", if i == 1 then "" else "s" ]
  putStrLn ""
  summarize s as r

runOS'' :: [MWord] -> Integer -> Integer -> IO ()
runOS'' = runState osSyscalls os0

runOS' :: Integer -> Integer -> IO ()
runOS' = runOS'' [osInfo^.osSharedAddress]

runOS :: Integer -> IO ()
runOS = runOS' 3
