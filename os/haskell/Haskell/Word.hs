{-# LANGUAGE DataKinds, KindSignatures, ScopedTypeVariables, LambdaCase #-}
module Haskell.Word (
  Word(), coqWord,
  Signed(..),
  wordBits, signedBits,
  word, signed,
  unsignedWord, signedWord, signedValue,
  KnownNat
  ) where

import Word hiding (Word)
import qualified Word as Word

import GHC.TypeLits
import Control.Applicative
import Data.Function
import Data.Bits
import Data.Coerce

-- Words are by default (ordering, arithmetic, printing) unsigned
newtype Word (n :: Nat) = Word { coqWord :: Coq_word }
                        deriving (Eq, Ord)

newtype Signed (n :: Nat) = Signed { getSigned :: Word n }
                          deriving Eq

instance Show (Word n) where
  showsPrec p = showsPrec p . unsignedWord

instance KnownNat n => Show (Signed n) where
  showsPrec p = showsPrec p . signedValue

wordBits :: KnownNat n => Word n -> Integer
wordBits = natVal

signedBits :: KnownNat n => Signed n -> Integer
signedBits = natVal

word :: KnownNat n => proxy n -> Integer -> Word n
word = (Word .) . as_word . natVal

signed :: KnownNat n => proxy n -> Integer -> Signed n
signed = coerce . word

unsignedWord :: Word n -> Integer
unsignedWord = ord_of_word __ . coqWord

signedWord :: KnownNat n => Word n -> Integer
signedWord = int_of_word <$> wordBits <*> coqWord

signedValue :: KnownNat n => Signed n -> Integer
signedValue = signedWord . getSigned

liftWord1 :: KnownNat n
          => (Integer -> Coq_word -> Coq_word)
          -> (Word n -> Word n)
liftWord1 op x = Word $ op (wordBits x) (coqWord x)

liftWord2 :: KnownNat n
          => (Integer -> Coq_word -> Coq_word -> Coq_word)
          -> (Word n -> Word n -> Word n)
liftWord2 op x y = Word $ op (wordBits x) (coqWord x) (coqWord y)

-- Arithmetic treats words as unsigned
instance KnownNat n => Num (Word n) where
  (+)    = liftWord2 addw
  (-)    = liftWord2 subw
  (*)    = liftWord2 mulw
  negate = liftWord1 oppw
  fromInteger 0    = Word . zerow $ wordBits (__ :: Word n)
  fromInteger 1    = Word . onew  $ wordBits (__ :: Word n)
  fromInteger (-1) = Word . monew $ wordBits (__ :: Word n)
  fromInteger n    = word (__ :: Word n) n
  abs = id
  signum x | x == 0    = 0
           | otherwise = 1

instance KnownNat n => Real (Word n) where
  toRational = fromIntegral

instance KnownNat n => Integral (Word n) where
  (Word (Word.Word m)) `quotRem` (Word (Word.Word n))
    | n == 0 = error "Integral.quotRem{Word n}: division by zero"
    | otherwise = let (q,r) = m `quotRem` n
                  in (Word (Word.Word q), Word (Word.Word r))
  toInteger = unsignedWord

instance KnownNat n => Enum (Word n) where
  toEnum   = fromIntegral
  fromEnum = fromIntegral
  
  succ w | w == maxBound =
             error "Enum.succ{Word n}: tried to take `succ' of maxBound"
         | otherwise =
           w + 1
  pred w | w == minBound =
             error "Enum.succ{Word n}: tried to take `succ' of minBound"
         | otherwise =
           w - 1

  enumFrom       m      = enumFromTo m maxBound
  enumFromTo     m    n = map (Word . Word.Word) [unsignedWord m .. unsignedWord n]
  enumFromThen   m m'   = enumFromThenTo m m' (if m < m' then maxBound else minBound)
  enumFromThenTo m m' n = map (Word . Word.Word) [unsignedWord m, unsignedWord m' .. unsignedWord n]

instance KnownNat n => Bounded (Word n) where
  minBound = Word . zerow $ wordBits (__ :: Word n)
  maxBound = Word . monew $ wordBits (__ :: Word n)

-- shift and rotate assume their arguments are in range
instance KnownNat n => Bits (Word n) where
  (.&.)      = liftWord2 andw
  (.|.)      = liftWord2 orw
  xor        = liftWord2 xorw
  complement = liftWord1 negw
  
  w `shiftL` d = Word $ shlw (wordBits w) (coqWord w) (as_word (wordBits w) $ fromIntegral d)
  shiftR       = ((Word . Word.Word) .) . shiftR . unsignedWord
  
  w `rotateL` d = let w'   = unsignedWord  w
                      k    = finiteBitSize w
                      mask = (1 `shiftL` k) - 1
                  in Word . Word.Word $ ((w' `shiftL` d) .|. (w' `shiftR` (k-d))) .&. mask
  w `rotateR` d = let w'   = unsignedWord  w
                      k    = finiteBitSize w
                      mask = (1 `shiftL` k) - 1
                  in Word . Word.Word $ ((w' `shiftR` d) .|. (w' `shiftL` (k-d))) .&. mask
  
  bit      = bitDefault
  testBit  = testBitDefault
  popCount = popCountDefault
  
  bitSizeMaybe = Just . finiteBitSize
  bitSize      = finiteBitSize
  isSigned     = const False
  
instance KnownNat n => FiniteBits (Word n) where
  finiteBitSize = fromInteger . wordBits

instance KnownNat n => Ord (Signed n) where
  compare = compare `on` signedValue

instance KnownNat n => Num (Signed n) where
  (+)    = coerce ((+)    :: Word n -> Word n -> Word n)
  (-)    = coerce ((-)    :: Word n -> Word n -> Word n)
  (*)    = coerce ((*)    :: Word n -> Word n -> Word n)
  negate = coerce (negate :: Word n -> Word n)
  fromInteger = Signed . fromInteger
  abs x | x < 0     = negate x
        | otherwise = x
  signum x = case x `compare` 0 of
               LT -> -1
               EQ ->  0
               GT ->  1

instance KnownNat n => Real (Signed n) where
  toRational = fromIntegral

instance KnownNat n => Integral (Signed n) where
  m `quotRem` n
    | n == 0 = error "Integral.quotRem{Signed n}: division by zero"
    | otherwise = let (q,r) = signedValue m `quotRem` signedValue n
                  in (fromInteger q, fromInteger r)
  
  m `divMod` n
    | n == 0 = error "Integral.divMod{Signed n}: division by zero"
    | otherwise = let (q,r) = signedValue m `divMod` signedValue n
                  in (fromInteger q, fromInteger r)
  
  toInteger = signedValue

instance KnownNat n => Enum (Signed n) where
  toEnum   = fromIntegral
  fromEnum = fromIntegral
  
  succ w | w == maxBound =
             error "Enum.succ{Signed n}: tried to take `succ' of maxBound"
         | otherwise =
           w + 1
  pred w | w == minBound =
             error "Enum.succ{Signed n}: tried to take `succ' of minBound"
         | otherwise =
           w - 1

  enumFrom       m      = enumFromTo m maxBound
  enumFromTo     m    n = map fromInteger [signedValue m .. signedValue n]
  enumFromThen   m m'   = enumFromThenTo m m' (if m < m' then maxBound else minBound)
  enumFromThenTo m m' n = map fromInteger [signedValue m, signedValue m' .. signedValue n]

instance KnownNat n => Bounded (Signed n) where
  minBound = complement maxBound
  maxBound = Signed (maxBound `shiftR` 1)

-- shift and rotate assume their arguments are in range
instance KnownNat n => Bits (Signed n) where
  (.&.)      = coerce ((.&.)      :: Word n -> Word n -> Word n)
  (.|.)      = coerce ((.|.)      :: Word n -> Word n -> Word n)
  xor        = coerce (xor        :: Word n -> Word n -> Word n)
  complement = coerce (complement :: Word n -> Word n)
  shiftL     = coerce (shiftL     :: Word n -> Int -> Word n)
  rotate     = coerce (rotate     :: Word n -> Int -> Word n)

  shiftR = (fromInteger .) . shiftR . signedValue
  
  bit      = bitDefault
  testBit  = testBitDefault
  popCount = popCountDefault
  
  bitSizeMaybe = Just . finiteBitSize
  bitSize      = finiteBitSize
  isSigned     = const True
  
instance KnownNat n => FiniteBits (Signed n) where
  finiteBitSize = fromInteger . signedBits
