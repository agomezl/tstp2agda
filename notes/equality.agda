open import Data.Nat using (ℕ)

module equality (n : ℕ) where


open import Data.Fin  using (Fin; zero; suc; #_)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Bool hiding (_≟_)
open import Data.Bool renaming (_∧_ to _&&_; _∨_ to _||_)

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import Relation.Nullary.Decidable using (⌊_⌋)

-- infix 5 _+_

data Cmd : Set where
  No : Fin n → Cmd
  _∥_ : (a b : Cmd) → Cmd

infix 8 _∥_
infix 7 _$>_

History : Set
History = List Cmd

data _$>_ : (_ : History)(_ : Cmd) → Set where
  intro : ∀ {h} {a} → (a ∷ h) $> a
  app : ∀ {h} {a b} → h $> a → h $> b → h $> a ∥ b

equal? : (a b : Cmd) → Bool
equal? (No x) (No x₁) = ⌊ x Data.Fin.Properties.≟ x₁ ⌋
equal? (No x) (y ∥ y₁) = false
equal? (x ∥ x₁) (No x₂) = false
equal? (x ∥ x₁) (y ∥ y₁) = (equal? x y) && (equal? x₁ y₁)

lem-subst : ∀ {h} {a} → (b : Cmd) → equal? a b ≡ true → h $> a → h $> b
lem-subst = {!!}
