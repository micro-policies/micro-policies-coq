{-# LANGUAGE OverloadedStrings #-}
module Haskell.Inspect where

import Data.List

import Haskell.Util
import Haskell.Types
import Haskell.Word
import Haskell.Machine
import Haskell.Pretty

import Data.Map (Map)
import qualified Data.Map as M

import qualified Os

inspectWord :: MWord -> Doc
inspectWord w =
  let ppp x = parens $ pPrint x -- DMR
      s = Signed $ mwordWord w
  in case decodeInstr w of
       Just i  -> i <&> if s < 0 then pPrint (w,s) else ppp w
       Nothing -> w <&> if s < 0 then ppp s        else empty

inspectInstr :: MWord -> Doc
inspectInstr w = maybe (pPrint w) pPrint $ decodeInstr w

inspectAtom :: Pretty t => Atom MWord t -> Doc
inspectAtom (w :@ t) = inspectWord w <&> taggedOp <&> t

inspectMaybe :: Pretty t => Maybe (Atom MWord t) -> Doc
inspectMaybe = maybe "<missing>" inspectAtom

inspectPieceAtIndex :: (Pretty t, Ord k)
                    => (s -> Map k (Atom MWord t)) -> s -> k -> Doc
inspectPieceAtIndex f s i = inspectMaybe $ M.lookup i (f s)

inspectAddr :: State -> MWord -> Doc
inspectAddr = inspectPieceAtIndex mem

-- No, these next two should use `pPrint' for atoms instead of
-- `inspectAtom`... or should they?  ACTUALLY, `inspectAtom` should be
-- cleverer about when to space out the tag... and then there's columning to
-- handle....

inspectPC :: State -> Doc
inspectPC = inspectAtom . pc

inspectReg :: State -> Reg -> Doc
inspectReg = inspectPieceAtIndex regs

inspectAddrs' :: (MWord -> String) -> State -> [MWord] -> [Doc]
inspectAddrs' ashow s addrs = map (hcat . map text)
                            $ transpose [ padToMatch AlignRight ' ' addrColumn
                                        , padToMatch AlignLeft  ' ' valueColumn
                                        , tagColumn ]
  where
    atomColumn missing ppp get =
      map (\i -> show . maybe missing ppp . fmap get $ M.lookup i (mem s)) addrs
    addrColumn  = map ((++ ": ") . ashow) addrs
    valueColumn = atomColumn "<missing>" inspectInstr          val
    tagColumn   = atomColumn empty       ((" @" <+>) . pPrint) tag

inspectAddrs :: State -> [MWord] -> Doc
inspectAddrs = (vcat .) . inspectAddrs' show

inspectAroundPC' :: (MWord -> String) -> State -> Integer -> [Doc]
inspectAroundPC' ashow s r =
  let pcA     = toInteger . val $ pc s
      maxAddr = toInteger $ if M.null (mem s) then 0 else fst . M.findMax $ mem s
      addrs   = [mword $ max (pcA - r) 0 .. mword $ min (pcA + r) maxAddr]
  in inspectAddrs'
       (\i -> (if i == mword pcA
                 then "[pc] "
                 else "     ")
           ++ ashow i)
       s
       (if null addrs then [mword pcA] else addrs)

inspectAroundPC :: State -> Integer -> Doc
inspectAroundPC = (vcat .) . inspectAroundPC' show

inspectRegs :: State -> [Reg] -> Doc
inspectRegs s rs = vcat . map (hcat . map text)
                  $ transpose [ padToMatch AlignLeft  ' ' $ map show rs
                              , valueColumn ]
  where
    valueColumn =
      map (\i -> show . maybe " <missing>" ((" ->" <+>) . pPrint)
                      . fmap val
                      $ M.lookup i (regs s))
          rs

inspectRegFile :: State -> Doc
inspectRegFile = flip inspectRegs [0 .. reg Os.user_reg_max]
