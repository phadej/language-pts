module Language.PTS.Sym where

import Data.Char     (isDigit)
import Data.Function (on)
import Data.String   (IsString (..))
import Data.Text     (Text)

-- | Symbols.
newtype Sym = Sym Text
  deriving (Eq, Ord)

instance Show Sym where
    showsPrec d (Sym s) = showsPrec d s

instance IsString Sym where
    fromString = Sym . fromString . f where
        f s | all isDigit s = s
            | otherwise     = map subDigit s

-- | Irrelevant symbols. Are all equal.
--
-- >>> "a" == ("b" :: IrrSym)
-- True
newtype IrrSym = IrrSym Sym

instance Eq IrrSym where
    _ == _ = True

instance Ord IrrSym where
    compare _ _ = EQ

instance Show IrrSym where
    showsPrec d (IrrSym s) = showsPrec d s

instance IsString IrrSym where
    fromString = IrrSym . fromString

-- | Two irrelevant symbols. Either one.
--
-- Essentially a 'Bool'.
--
data IrrSym2
    = IrrSym1 Sym
    | IrrSym2 Sym

irrSym2fold :: a -> a -> IrrSym2 -> a
irrSym2fold x _ (IrrSym1 _) = x
irrSym2fold _ y (IrrSym2 _) = y

irrSym2Bool :: IrrSym2 -> Bool
irrSym2Bool = irrSym2fold False True

instance Eq IrrSym2 where
    (==) = (==) `on` irrSym2Bool

instance Ord IrrSym2 where
    compare = compare `on` irrSym2Bool

instance Show IrrSym2 where
    showsPrec d (IrrSym1 s) = showsPrec d s
    showsPrec d (IrrSym2 s) = showsPrec d s

subDigit :: Char -> Char
subDigit '0' = '₀'
subDigit '1' = '₁'
subDigit '2' = '₂'
subDigit '3' = '₃'
subDigit '4' = '₄'
subDigit '5' = '₅'
subDigit '6' = '₆'
subDigit '7' = '₇'
subDigit '8' = '₈'
subDigit '9' = '₉'
subDigit c   = c

unsubDigit :: Char -> Char
unsubDigit '₀' = '0'
unsubDigit '₁' = '1'
unsubDigit '₂' = '2'
unsubDigit '₃' = '3'
unsubDigit '₄' = '4'
unsubDigit '₅' = '5'
unsubDigit '₆' = '6'
unsubDigit '₇' = '7'
unsubDigit '₈' = '8'
unsubDigit '₉' = '9'
unsubDigit c   = c

-- $setup
-- >>> :set -XOverloadedStrings
