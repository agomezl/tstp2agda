module Deep (n : ℕ) where

open import Data.Bool public using (Bool; true; false; not)
open import Data.Bool public renaming (_∧_ to _&&_) hiding (_∨_)
open import Data.Fin public using (Fin; zero; suc; #_)
open import Data.Nat public using (ℕ; zero; suc)
open import Data.Vec public using (Vec; lookup)
open import Data.List public using (List; []; _∷_)

open import Function public using (_$_)

open import Relation.Binary.PropositionalEquality public using (_≡_; refl)


-- The parameter of the whole formalization
-- n : ℕ
-- n = 5


--       the number of propositional atoms
--           ↓
data Prop : Set where
  Var : Fin n → Prop
  ⊤ ⊥ : Prop
  _∧_ : (φ ψ : Prop) → Prop
  ¬_  : (φ : Prop) → Prop

_!_ : {A : Set}{n : ℕ} → Vec A n → Fin n → A
v ! idx = lookup idx v


-- Valuation
Val : Set
Val = Vec Bool n

--          formula     valuation
--               ↓        ↓
⟦_⟧ : Prop → Val → Bool
⟦ Var i ⟧  v = v ! i
⟦ ⊤ ⟧      v = true
⟦ ⊥ ⟧      v = false
⟦ p ∧ q ⟧  v = ⟦ p ⟧ v && ⟦ q ⟧ v
⟦ ¬ p ⟧    v = not (⟦ p ⟧ v)

-- the missing conectives

_∨_ : Prop → Prop → Prop
p ∨ q = (¬ p) ∧ (¬ q)

_⇒_ : Prop → Prop → Prop
p ⇒ q  = (¬ p) ∨ q


_⇔_ : Prop → Prop → Prop
p ⇔ q = (p ⇒ q) ∧ (q ⇒ p)

-- Ctxt : Set
-- Ctxt = List Prop


-- _·_ : Ctxt → Prop → Ctxt
-- Γ · φ = φ ∷ Γ

-- ∅ : Ctxt
-- ∅ = []

data Ctxt : ℕ → Set where
  ∅ : Ctxt zero
  _·_ : {l : ℕ} → Ctxt l → Prop → Ctxt (suc l)

infix 10 ¬_
infixl 7 _∧_
infixr 6 _⇒_
infix 4 _⊢_
infixl 5 _·_
infixl 7 _∨_

data _⊢_ : {l : ℕ} (Γ  : Ctxt l)(ψ : Prop) → Set where
  assume   : ∀{l}{Γ : Ctxt l} → (φ : Prop)    → (Γ · φ) ⊢ φ
  weaken   : ∀{l}{Γ : Ctxt l} {φ ψ}  → Γ ⊢ ψ
                                    -- ----------
                                     → (Γ · φ) ⊢ ψ
  ⊤-intro  : ∀{l}{Γ : Ctxt l}        → Γ ⊢ ⊤
  ⊥-elim   : ∀{l}{Γ : Ctxt l} {φ}    → Γ ⊢ ⊥
                                    -- ----------
                                     → Γ ⊢ φ
  ¬-intro  : ∀{l}{Γ : Ctxt l} {φ}    → (Γ · φ) ⊢ ⊥
                                    -- ----------
                                     → Γ ⊢ (¬ φ)
  RAA      : ∀{l}{Γ : Ctxt l} {φ}    → Γ · (¬ φ) ⊢ ⊥
                                    -- --------------
                                     → Γ ⊢ φ
  ∧-intro  : ∀{l}{Γ : Ctxt l} {φ ψ}  → Γ ⊢ φ → Γ ⊢ ψ
                                    -- --------------
                                     → Γ ⊢ (φ ∧ ψ)
  ∧-proj₁  : ∀{l}{Γ : Ctxt l} {φ ψ}  → Γ ⊢ (φ ∧ ψ)
                                    -- ----------
                                     → Γ ⊢ φ

  ∧-proj₂  : ∀{l}{Γ : Ctxt l} {φ ψ}  → Γ ⊢ (φ ∧ ψ)
                                    -- ------------
                                     → Γ ⊢ ψ
  pem      : ∀{l}{Γ : Ctxt l} {φ}    → Γ ⊢ (φ ∨ (¬ φ))

  -- extra deduction rules

  ∨-intro₁ : ∀{l}{Γ : Ctxt l} {φ ψ}  → Γ ⊢ φ
                                    -- -----------
                                     → Γ ⊢ (φ ∨ ψ)
  ∨-intro₂ : ∀{l}{Γ : Ctxt l} {φ ψ}  → Γ ⊢ ψ
                                    -- -----------
                                     → Γ ⊢ (φ ∨ ψ)
  ∨-elim  : ∀{l}{Γ : Ctxt l} {φ ψ χ} → (Γ · φ) ⊢ χ
                                     → (Γ · ψ) ⊢ χ
                                    -- ------------
                                     → (Γ · (φ ∨ ψ)) ⊢ χ
  ⇒-intro  : ∀{l}{Γ : Ctxt l} {φ ψ}  → (Γ · φ) ⊢ ψ
                                    -- -----------
                                     → Γ ⊢ (φ ⇒ ψ)
  ⇒-elim   : ∀{l}{Γ : Ctxt l} {φ ψ}  → Γ ⊢ (φ ⇒ ψ) → Γ ⊢ φ
                                    -- -------------------
                                     → Γ ⊢ ψ
--  --------------------------------------------------------------

p : Prop
p = Var (# 0)

-- axiom : ∀{l}(Γ : Ctxt l) → (φ : Prop) → (Γ · φ) ⊢ φ
-- axiom l ψ = assume{Γ = l}{φ = ψ}

-- ¬-rule : ∀ {Γ} {φ} → Γ ⊢ (¬ ¬ φ) ⇒ φ
-- ¬-rule = ⇒-elim assume assume

-- axiom Γ (Var x) = assume{Γ = Γ }{φ = Var x}
-- axiom Γ ⊤ = ⊤-intro
-- axiom Γ ⊥ = assume{Γ = Γ}{φ = ⊥}
-- axiom Γ (φ₁ ∧ φ₂) = assume{φ = (φ₁ ∧ φ₂)}
-- axiom Γ (¬ ψ) = assume{φ = (¬ ψ)}

-- I : ∀ {Γ} {φ} → Γ ⊢ (φ ⇒ φ)
-- I = ⇒-intro assume

-- distrib : ∀ {Γ P Q R} → Γ ⊢ P ∧ (Q ∨ R) ⇒ (P ∧ Q) ∨ (P ∧ R)
-- distrib = abs (elim (case (left (pair (weak ass) ass)) (right (pair (weak ass) ass))))


-- [_] : ∀ {l} Prop → Ctxt l
-- [ x ] = ∅ · x

-- e : ∀ {Γ} {φ ψ : Prop} → Γ ⊢ (φ ∧ ψ) ⇒ (ψ ∧ φ)
-- e {Γ} {φ} {ψ} = ∧-intro (assume{φ} assume
-- exampleB : ∀ {φ} → [ (φ ⇒ ⊥) ] · φ ⊢ ⊥
-- exampleB = ⇒-intro assume assume


exampleB : ∀ {l} {Γ : Ctxt l}{φ ψ : Prop} → Γ ⊢ ((φ ∧ ψ) ⇒ (ψ ∧ φ))
exampleB {φ = φ}{ψ} = ⇒-intro (∧-intro (∧-proj₂ (assume (φ ∧ ψ))) (∧-proj₁ {ψ = ψ}(assume (φ ∧ ψ)))) -- ⇒-intro (∧-intro (∧-proj₂ assume) (∧-proj₁ assume))

-- ---------------------------------------------------------------
-- satisfies : Prop → Val → Set
-- satisfies φ v = ⟦ φ ⟧ v ≡ true

-- tautology : Prop → Set
-- tautology φ = ∀ (v : Val) → satisfies φ v

-- _≈_ : Prop → Prop → Set
-- -- p ≈ q = tautology (p ⇔ q)
