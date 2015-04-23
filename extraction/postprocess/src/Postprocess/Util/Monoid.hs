module Postprocess.Util.Monoid (nonemptyIfNonnull, (?+++), (+++?), (??++), (++??)) where

import Data.Monoid

nonemptyIfNonnull :: Monoid m => [a] -> [m]
nonemptyIfNonnull xs = [mempty | not $ null xs]

(?+++), (+++?), (??++), (++??) :: Monoid m => [m] -> [m] -> [m]
xs ?+++ ys = xs ++ nonemptyIfNonnull xs ++ ys
xs +++? ys = xs ++ nonemptyIfNonnull ys ++ ys
xs ??++ ys = nonemptyIfNonnull xs ++ xs ++ nonemptyIfNonnull xs ++ ys
xs ++?? ys = xs ++ nonemptyIfNonnull ys ++ ys ++ nonemptyIfNonnull ys
infixr 5 ?+++ , +++? , ??++ , ++??
