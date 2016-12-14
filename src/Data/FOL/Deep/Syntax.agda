open import Data.Nat public using (ℕ; zero; suc)

-- The parameter of the whole formalization
--                              ↓
module Data.FOL.Deep.Syntax (n : ℕ) where

open import Data.Bool public using (Bool; true; false; not)
open import Data.Bool public renaming (_∧_ to _&&_; _∨_ to _||_)
open import Data.Fin  public using (Fin; zero; suc; #_)
open import Data.List public using (List; []; _∷_; _++_; [_])
open import Data.Vec  public using (Vec; lookup)

open import Function  public using (_$_)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)

Type = Set

-- Propositions
data Prop : Type where
  Var         : Fin n → Prop
  ⊤ ⊥         : Prop
  _∧_ _∨_ _⇒_ : (φ ψ  : Prop) → Prop
  ¬_          : (φ : Prop) → Prop

-- Precedence of operators
infix  11 ¬_
infixl 8  _∧_ _∨_
infixr 7  _⇒_

-- Context: list (set) of premises
Ctxt : Type
Ctxt = List Prop

infixl 5 _,_
_,_ : Ctxt → Prop → Ctxt
Γ , φ =  Γ ++ [ φ ]

∅ : Ctxt
∅ = []

infix 30 _⨆_
_⨆_ : Ctxt → Ctxt → Ctxt
Γ ⨆ Δ = Γ ++ Δ

infix 4 _∈_
data _∈_ (φ : Prop) : Ctxt → Type where
  here    : ∀ {Γ} → φ ∈ Γ , φ
  there   : ∀ {Γ} → (ψ : Prop) → φ ∈ Γ → φ ∈ Γ , ψ
  ⨆-ext   : ∀ {Γ} → (Δ : Ctxt) → φ ∈ Γ → φ ∈ Γ ⨆ Δ

_⊆_ : Ctxt → Ctxt → Type
Γ ⊆ Η = ∀ {φ : Prop} → φ ∈ Γ → φ ∈ Η

infix 3 _⊢_
data _⊢_ : (Γ : Ctxt)(φ : Prop) → Type where
  assume   : ∀ {Γ : Ctxt} → (φ : Prop)           → Γ , φ ⊢ φ

  axiom    : ∀ {Γ : Ctxt} → (φ : Prop)           → φ ∈ Γ
                                                 → Γ ⊢ φ

  weaken   : ∀ {Γ : Ctxt} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                                 → Γ , ψ ⊢ φ

  weaken-Δ₁ : ∀ {Γ : Ctxt} {φ} → (Δ : Ctxt)      → Γ ⊢ φ
                                                 → Γ ⨆ Δ ⊢ φ

  weaken-Δ₂ :  ∀ {Γ : Ctxt} {φ} → (Δ : Ctxt)     → Γ ⊢ φ
                                                 → Δ ⨆ Γ ⊢ φ

  ⊤-intro  : ∀ {Γ : Ctxt}                        → Γ ⊢ ⊤

  ⊥-elim   : ∀ {Γ : Ctxt} → (φ : Prop)           → Γ ⊢ ⊥
                                                 → Γ ⊢ φ

  ¬-intro  : ∀ {Γ : Ctxt} {φ}                    → Γ , φ ⊢ ⊥
                                                 → Γ ⊢ ¬ φ

  ¬-elim   : ∀ {Γ : Ctxt} {φ}                    → Γ ⊢ ¬ φ → Γ ⊢ φ
                                                 → Γ ⊢ ⊥

  RAA      : ∀ {Γ : Ctxt} {φ}                    → Γ , ¬ φ ⊢ ⊥
                                                 → Γ ⊢ φ

  ∧-intro  : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ → Γ ⊢ ψ
                                                 → Γ ⊢ φ ∧ ψ

  ∧-proj₁  : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                                 → Γ ⊢ φ

  ∧-proj₂  : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ ∧ ψ
                                                 → Γ ⊢ ψ

  PEM      : ∀ {Γ : Ctxt} {φ}                    → Γ ⊢ φ ∨ ¬ φ


  ∨-intro₁ : ∀ {Γ : Ctxt} {φ} → (ψ : Prop)       → Γ ⊢ φ
                                                 → Γ ⊢ φ ∨ ψ

  ∨-intro₂ : ∀ {Γ : Ctxt} {ψ} → (φ : Prop)       → Γ ⊢ ψ
                                                 → Γ ⊢ φ ∨ ψ

  ∨-elim  : ∀ {Γ : Ctxt} {φ ψ χ}                 → Γ , φ ⊢ χ
                                                 → Γ , ψ ⊢ χ
                                                 → Γ , φ ∨ ψ ⊢ χ

  ⇒-intro  : ∀ {Γ : Ctxt} {φ ψ}                  → Γ , φ ⊢ ψ
                                                 → Γ ⊢ φ ⇒ ψ

  ⇒-elim   : ∀ {Γ : Ctxt} {φ ψ}                  → Γ ⊢ φ ⇒ ψ → Γ ⊢ φ
                                                 → Γ ⊢ ψ
