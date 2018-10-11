module Language.PTS.Sym where

import Data.String (IsString (..))
import Data.Text (Text)


-- | Symbols.
newtype Sym = Sym Text
  deriving (Eq, Ord)

instance Show Sym where
    showsPrec d (Sym s) = showsPrec d s

instance IsString Sym where
    fromString = Sym . fromString

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

-- $setup
-- >>> :set -XOverloadedStrings
