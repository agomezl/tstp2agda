open import Data.Nat using (ℕ)

-- The parameter of the whole formalization
--                    ↓
module Data.FOL.Deep.Semantics (n : ℕ) where

open import Data.FOL.Deep.Syntax n

open import Data.Bool using (Bool; true; false; not)
open import Data.Bool renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Fin  using (Fin; zero; suc; #_)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Vec  using (Vec; lookup)
open import Function  using (_$_)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)

_!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
v ! idx = lookup idx v

-- Valuation vector
Val : Set
Val = Vec Bool n

-- Semantics:
--   formula valuation
--     ↓      ↓
⟦_⟧ : Prop → Val → Bool
⟦ Var i ⟧  v = v ! i
⟦ ⊤ ⟧      v = true
⟦ ⊥ ⟧      v = false
⟦ p ∧ q ⟧  v = ⟦ p ⟧ v && ⟦ q ⟧ v
⟦ p ∨ q ⟧  v = ⟦ p ⟧ v || ⟦ q ⟧ v
⟦ p ⇒ q ⟧  v = not (⟦ p ⟧ v) || ⟦ q ⟧ v
⟦ ¬ p ⟧    v = not (⟦ p ⟧ v)

satisfies : Prop → Val → Set
satisfies φ v = ⟦ φ ⟧ v ≡ true

tautology : Prop → Set
tautology φ = ∀ (v : Val) → satisfies φ v

_≅_ : Prop → Prop → Set
p ≅ q = tautology $ p ⇒ q ∧ q ⇒ p

