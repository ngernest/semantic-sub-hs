module Types.Base
  ( BaseTy (..),
    Base (..),
    emptyBase,
    anyBase,
    baseOr,
    baseAnd,
    baseDiff,
    baseNot,
  )
where

import Data.Set (Set, empty, intersection, union, (\\))

-- -----------------------------------------------------------------------------
--                         3.2 Base DNF Representation
-- -----------------------------------------------------------------------------

-- | Base types
data BaseTy = T | F | Z
  deriving (Eq, Show, Ord)

-- 1st arg: polarity flag (is the union negated or not)
-- 2nd arg: set of base types in the union
data Base = Base Bool (Set BaseTy)
  deriving (Eq, Show, Ord)

-- | Bottom base type (denotes no base type values)
-- (positive empty set, i.e. it is the case that this type
-- contains no base values)
emptyBase :: Base
emptyBase = Base True empty

-- | Top base type representing all base type values
-- (negated empty set, i.e. it is *not* the case that this type
-- contains no base values)
anyBase :: Base
anyBase = Base False empty

-- -----------------------------------------------------------------------------
--                          3.2.1 Base DNF Operations
-- -----------------------------------------------------------------------------

-- | Set-theoretic union for base types
baseOr :: Base -> Base -> Base
baseOr (Base True pos1) (Base True pos2) =
  Base True (pos1 `union` pos2)
baseOr (Base True pos) (Base False neg) =
  Base False (neg \\ pos)
baseOr (Base False neg) (Base True pos) =
  Base False (neg \\ pos)
baseOr (Base False neg1) (Base False neg2) =
  Base False (neg1 `intersection` neg2)

-- | Set-theoretic interesction for base types
baseAnd :: Base -> Base -> Base
baseAnd (Base True pos1) (Base True pos2) =
  Base True (pos1 `intersection` pos2)
baseAnd (Base True pos) (Base False neg) =
  Base True (pos \\ neg)
baseAnd (Base False neg) (Base True pos) =
  Base True (pos \\ neg)
baseAnd (Base False neg1) (Base False neg2) =
  Base False (neg1 `union` neg2)

-- | Set-difference interesction for base types
baseDiff :: Base -> Base -> Base
baseDiff (Base True pos1) (Base True pos2) =
  Base True (pos1 \\ pos2)
baseDiff (Base True pos) (Base False neg) =
  Base True (pos `intersection` neg)
baseDiff (Base False neg) (Base True pos) =
  Base False (pos `union` neg)
baseDiff (Base False neg1) (Base False neg2) =
  Base True (neg2 \\ neg1)

-- | Negation of base types (just flips the polarity flag)
baseNot :: Base -> Base
baseNot (Base sign bs) = Base (not sign) bs
