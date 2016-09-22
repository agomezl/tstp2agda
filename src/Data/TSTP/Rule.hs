
-- | Data.TSTP.Rule module


module Data.TSTP.Rule where


-- | Deduction rule applied.
data Rule = Canonicalize
          | Negate
          | NewRule String
          | Simplify
          | Strip
          deriving (Eq, Ord, Show, Read)
