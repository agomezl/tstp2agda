open import Data.Nat public using (ℕ; zero; suc)

-- The parameter of the whole formalization
--                    ↓
module Data.FOL.Deep (n : ℕ) where

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

_≅_ : Prop → Prop → Set
p ≅ q = tautology $ p ⇒ q ∧ q ⇒ p

-- Context: list (set) of premises
Ctxt : Set
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
data _∈_ (φ : Prop) : Ctxt → Set where
  here    : ∀ {Γ} → φ ∈ Γ , φ
  there   : ∀ {Γ} → (ψ : Prop) → φ ∈ Γ → φ ∈ Γ , ψ
  ⨆-ext   : ∀ {Γ} → (Δ : Ctxt) → φ ∈ Γ → φ ∈ Γ ⨆ Δ

_⊆_ : Ctxt → Ctxt → Set
Γ ⊆ Η = ∀ {φ : Prop} → φ ∈ Γ → φ ∈ Η

--
data True : Set where
  tt : True

data False : Set where

-- infix 4 _∋_
-- _∋_ : Ctxt → Prop → Set
-- [] ∋ _ = False
-- (φ ∷ fs) ∋ ψ with (eq φ ψ)
-- ... | true  = True
-- ... | false = fs ∋ ψ


--

infix 3 _⊢_
data _⊢_ : (Γ : Ctxt)(φ : Prop) → Set where
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

  pem      : ∀ {Γ : Ctxt} {φ}                    → Γ ⊢ φ ∨ ¬ φ


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


----------------------------------------------------------------------


swap : ∀ {Γ : Ctxt} {φ ψ γ} → (Γ , φ , ψ) ⊢ γ → Γ , ψ , φ ⊢ ψ
swap {Γ} {φ = φ}{ψ} x =
  axiom {Γ = (Γ , ψ , φ)} ψ $
    there {Γ = Γ , ψ} φ $
      here {φ = ψ} {Γ = Γ}

-- van Dalen 4th Edition. Chapter 2. Section 2.4.
-- Theorem 2.4.4

th244a : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ φ ⇒ (ψ ⇒ φ)
th244a {Γ}{φ}{ψ = ψ} =
  ⇒-intro $
    ⇒-intro $
      weaken {φ = φ} ψ $
        assume {Γ = Γ} φ

th244b : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ φ ⇒ (¬ φ ⇒ ψ)
th244b {Γ}{φ = φ}{ψ = ψ} =
  ⇒-intro $
    ⇒-intro $
      ⊥-elim {Γ = (Γ , φ , ¬ φ)} ψ $
        ¬-elim
          (assume  {Γ = (Γ , φ)} (¬ φ))
          (weaken (¬ φ) (assume {Γ = Γ} φ))

th244c : ∀ {Γ : Ctxt} {φ ψ σ} → Γ ⊢ (φ ⇒ ψ) ⇒ ((ψ ⇒ σ) ⇒ (φ ⇒ σ))
th244c {Γ}{φ = φ}{ψ}{σ} =
  ⇒-intro $
     ⇒-intro $
       ⇒-intro $
         ⇒-elim {Γ = Γ , φ ⇒ ψ , ψ ⇒ σ , φ}
           (weaken φ $ assume {Γ = Γ , φ ⇒ ψ} $ ψ ⇒ σ)
            (⇒-elim {Γ = Γ , φ ⇒ ψ , ψ ⇒ σ , φ}
              (weaken φ $ weaken (ψ ⇒ σ) $ assume {Γ = Γ} $ φ ⇒ ψ)
              (assume {Γ = Γ , φ ⇒ ψ , ψ ⇒ σ} φ))

th244d : ∀ {Γ : Ctxt} {φ ψ} → Γ ⊢ (¬ ψ ⇒ ¬ φ) ⇒ (φ ⇒ ψ)
th244d {Γ} {φ = φ}{ψ} =
  ⇒-intro $
    ⇒-intro $
      RAA $
        ¬-elim {Γ = Γ , ¬ ψ ⇒ ¬ φ , φ , ¬ ψ}
          (⇒-elim
            (weaken (¬ ψ) $ weaken φ $ assume {Γ = Γ} $ ¬ ψ  ⇒ ¬ φ)
            (assume {Γ = Γ , ¬ ψ ⇒ ¬ φ , φ} $ ¬ ψ)
           )
          (weaken (¬ ψ) $ assume {Γ = Γ , ¬ ψ ⇒ ¬ φ} φ)

e244e : ∀ {Γ : Ctxt} {φ} → Γ ⊢ ¬ (¬ φ) ⇒ φ
e244e {Γ} {φ} =
  ⇒-intro $ RAA
    (¬-elim {Γ = Γ , ¬ (¬ φ) , ¬ φ}
      (weaken (¬ φ) $ assume {Γ = Γ} $ ¬ (¬ φ))
      (assume {Γ = Γ , ¬ (¬ φ)} $ ¬ φ))

e245b : ∀ {Γ Δ : Ctxt} {φ ψ} → Γ ⊢ φ → Δ , φ ⊢ ψ → Γ ⨆ Δ ⊢ ψ
e245b {Γ}{Δ = Δ} seq₁ seq₂ =
  ⇒-elim
    (weaken-Δ₂ Γ (⇒-intro seq₂))
    (weaken-Δ₁ Δ seq₁)
--


---
morgan₁ : ∀ {Γ} {φ ψ} → Γ ⊢ ¬ (φ ∧ ψ) ⇒ (¬ φ ∨ ¬ ψ)
morgan₁ {Γ} {φ}{ψ} =
  ⇒-intro {Γ = Γ} $
    RAA {Γ = Γ , ¬ (φ ∧ ψ)} {φ = ¬ φ ∨ ¬ ψ}
      (¬-elim {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)}
        (weaken (¬ (¬ φ ∨ ¬ ψ))
          (assume {Γ = Γ} (¬ (φ ∧ ψ))))
        (∧-intro
          (RAA {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} {φ = φ}
            (¬-elim {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ) , ¬ φ}
              (weaken (¬ φ) (assume {Γ = Γ , ¬ (φ ∧ ψ)} (¬ (¬ φ ∨ ¬ ψ))))
              (∨-intro₁
                (¬ ψ)
                (assume {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)}
                  (¬ φ)))))
          (RAA {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)} {φ = ψ}
            (¬-elim {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ) , ¬ ψ}
              (weaken (¬ ψ) (assume {Γ = Γ , ¬ (φ ∧ ψ)} (¬ (¬ φ ∨ ¬ ψ))))
              (∨-intro₂
                (¬ φ)
                (assume {Γ = Γ , ¬ (φ ∧ ψ) , ¬ (¬ φ ∨ ¬ ψ)}
                  (¬ ψ)))))))

---
{-
resolve : ∀ {Γ} {L C D} → Γ ⊢ L ∨ C → Γ ⊢ ¬ L ∨ D → Γ ⊢ C ∨ D
resolve =
  {!!}
-}

-- e245 Γ (Var x) Δ z = {!!}
-- e245 Γ ⊤ Δ z = ⊤-intro {Γ = (Γ ⨆ Δ)}
-- e245 Γ ⊥ Δ z = {!!} -- ∧-proj₁ {ψ = ⊥} $ e245 Γ (⊥ ∧ ⊥) Δ {!⊥-elim!}
-- e245 Γ (φ ∧ ψ) Δ z =
--   ∧-intro {Γ = (Γ ⨆ Δ)}
--     (e245 Γ φ Δ
--       (∧-proj₁ {ψ = ψ} z))
--     (e245 Γ ψ Δ
--       (∧-proj₂ z))
-- e245 Γ (φ ∨ φ₁) Δ z = {!!}
-- e245 Γ (φ ⇒ φ₂) Δ z = {!!}



-- I : ∀ {Γ} (φ : Prop) → Γ ⊢ φ ⇒ φ
-- I φ = ⇒-intro $ assume φ

-- exampleB : ∀ {Γ : Ctxt}{φ ψ : Prop} → Γ ⊢ φ ∧ ψ ⇒ ψ ∧ φ
-- exampleB {φ = φ}{ψ} =
--   ⇒-intro $
--     ∧-intro
--       (∧-proj₂ $ assume $ φ ∧ ψ)
--       (∧-proj₁ {ψ = ψ} $ assume $ φ ∧ ψ)
