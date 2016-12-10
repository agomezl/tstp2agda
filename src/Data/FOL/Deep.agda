open import Data.Nat public using (ℕ; zero; suc)

-- The parameter of the whole formalization
--                    ↓
module Data.FOL.Deep (n : ℕ) where

open import Data.Bool public using (Bool; true; false; not)
open import Data.Bool public renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Fin  public using (Fin; zero; suc; #_)
open import Data.List public using (List; []; _∷_)
open import Data.Vec  public using (Vec; lookup)

open import Function  public using (_$_)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)

Type = Set

-- Propositions
data Prop : Type where
  Var         : Fin n → Prop
  ⊤ ⊥         : Prop
  _∧_ _∨_ _⇒_ : (φ ψ : Prop) → Prop
  ¬_          : (φ : Prop) → Prop

-- Precedence of operators
infix  10 ¬_
infixl 7  _∧_ _∨_
infixr 6  _⇒_

-- About Valuation

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

_≈_ : Prop → Prop → Set
p ≈ q = tautology $ p ⇒ q ∧ q ⇒ p

-- Context: list (set) of premises
Ctxt : Set
Ctxt = List Prop

infixl 6 _·_
_·_ : Ctxt → Prop → Ctxt
Γ · φ = φ ∷ Γ

∅ : Ctxt
∅ = []

infix 5 _⊢_
data _⊢_ : (Γ : Ctxt)(φ : Prop) → Set where
  assume   : ∀ {Γ : Ctxt} → (φ : Prop)           → Γ · φ ⊢ φ

  weaken   : ∀ {Γ : Ctxt} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                                 → Γ · ψ ⊢ φ

  ⊤-intro  : ∀ {Γ : Ctxt}                        → Γ ⊢ ⊤

  ⊥-elim   : ∀ {Γ : Ctxt} → (φ : Prop)           → Γ ⊢ ⊥
                                                 → Γ ⊢ φ

  ¬-intro  : ∀ {Γ : Ctxt} {φ}                    → Γ · φ ⊢ ⊥
                                                 → Γ ⊢ ¬ φ

  RAA      : ∀ {Γ : Ctxt} {φ}                    → Γ · ¬ φ ⊢ ⊥
                                                 → Γ ⊢ φ

  ∧-intro  : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ → Γ ⊢ ψ
                                                 → Γ ⊢ φ ∧ ψ

  ∧-proj₁  : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                                 → Γ ⊢ φ

  ∧-proj₂  : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                                 → Γ ⊢ ψ
  pem      : ∀ {Γ : Ctxt} {φ}                    → Γ ⊢ φ ∨ ¬ φ


  ∨-intro₁ : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ
                                                 → Γ ⊢ φ ∨ ψ

  ∨-intro₂ : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ ψ
                                                 → Γ ⊢ φ ∨ ψ

  ∨-elim  : ∀ {Γ : Ctxt} {φ ψ χ}                 → Γ · φ ⊢ χ
                                                 → Γ · ψ ⊢ χ
                                                 → Γ · (φ ∨ ψ) ⊢ χ
  ⇒-intro  : ∀ {Γ : Ctxt} {φ ψ}                  → Γ · φ ⊢ ψ
                                                 → Γ ⊢ φ ⇒ ψ

  ⇒-elim   : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ ⇒ ψ → Γ ⊢ φ
                                                 → Γ ⊢ ψ


--

axiom : ∀ {Γ : Ctxt} (φ : Prop) → Γ · φ ⊢ φ
axiom = assume

I : ∀ {Γ} (φ : Prop) → Γ ⊢ φ ⇒ φ
I φ = ⇒-intro $ assume φ

exampleB : ∀ {Γ : Ctxt}{φ ψ : Prop} → Γ ⊢ φ ∧ ψ ⇒ ψ ∧ φ
exampleB {φ = φ}{ψ} =
  ⇒-intro $
    ∧-intro
      (∧-proj₂ $ assume $ φ ∧ ψ)
      (∧-proj₁ {ψ = ψ} $ assume $ φ ∧ ψ)
