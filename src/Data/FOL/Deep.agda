module Data.FOL.Deep where

open import Data.FOL.Shallow
open import Data.Nat.Base
open import Data.Vec

infixl 5 _▴_ _▾_ _⇒_

constrains :  ℕ  → Set₁
constrains zero    = Set
constrains (suc n) = {A : Set} → constrains n

data Fol : (n : ℕ) → Set  where
  _▴_ : {n : ℕ}   → Fol n → Fol n → Fol n
  _▾_ : {n : ℕ}   → Fol n → Fol n → Fol n
  _⇒_ : {n : ℕ}   → Fol n → Fol n → Fol n
  ν   : {n : ℕ} → (m : ℕ) → {less : m ≤ n} →  Fol n
  ∼   : {n : ℕ }  → Fol n → Fol n

δ : {n : ℕ } → Fol n → constrains n
δ a = {!!}
