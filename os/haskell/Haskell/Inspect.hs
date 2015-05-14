{-# LANGUAGE OverloadedStrings, PatternSynonyms #-}
module Haskell.Inspect where

import Control.Arrow hiding ((<+>))
import Data.List

import Haskell.Util
import Haskell.Types
import Haskell.Word
import Haskell.Machine
import Haskell.Pretty

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

inspectPieceAtIndex :: (Pretty t, Integral i)
                    => (s -> PartMap k (Atom MWord t)) -> s -> i -> Doc
inspectPieceAtIndex f s i = inspectMaybe . fmap snd $ f s ?? i

inspectAddr :: Integral i => State -> i -> Doc
inspectAddr = inspectPieceAtIndex mem

-- No, these next two should use `pPrint' for atoms instead of
-- `inspectAtom`... or should they?  ACTUALLY, `inspectAtom` should be
-- cleverer about when to space out the tag... and then there's columning to
-- handle....

inspectPC :: Integral i => State -> Doc
inspectPC = inspectAtom . pc

inspectReg :: Integral i => State -> i -> Doc
inspectReg = inspectPieceAtIndex regs

inspectAddrs' :: Integral i => (i -> String) -> State -> [i] -> [Doc]
inspectAddrs' ashow s addrs = map (hcat . map text)
                            $ transpose [ padToMatch AlignRight ' ' addrColumn
                                        , padToMatch AlignLeft  ' ' valueColumn
                                        , tagColumn ]
  where
    atomColumn missing ppp get =
      map (\i -> show . maybe missing ppp . fmap (get . snd) $ mem s ?? i) addrs
    addrColumn  = map ((++ ": ") . ashow) addrs
    valueColumn = atomColumn "<missing>" inspectInstr          val
    tagColumn   = atomColumn empty       ((" @" <+>) . pPrint) tag

inspectAddrs :: (Integral i, Show i) => State -> [i] -> Doc
inspectAddrs = (vcat .) . inspectAddrs' show

inspectAroundPC' :: (Integral i, Show i) => (i -> String) -> State -> i -> [Doc]
inspectAroundPC' ashow s r =
  let pcA   = fromIntegral . val $ pc s
      addrs = [max (pcA - r) 0 .. min (pcA + r) (genericLength $ mem s)]
  in inspectAddrs'
       (\i -> (if i == pcA
                 then "[pc] "
                 else "     ")
           ++ ashow i)
       s
       (if null addrs then [pcA] else addrs)

inspectAroundPC :: (Integral i, Show i) => State -> i -> Doc
inspectAroundPC = (vcat .) . inspectAroundPC' show

inspectRegs :: State -> [Reg] -> Doc
inspectRegs s rs = vcat . map (hcat . map text)
                  $ transpose [ padToMatch AlignLeft  ' ' $ map show rs
                              , valueColumn ]
  where
    valueColumn =
      map (\i -> show . maybe " <missing>" ((" ->" <+>) . pPrint)
                      . fmap (val . snd)
                      $ regs s ?? i)
          rs

inspectRegFile :: State -> Doc
inspectRegFile = flip inspectRegs [0 .. reg Os.user_reg_max]
