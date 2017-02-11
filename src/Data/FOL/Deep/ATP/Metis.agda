open import Data.Nat using (ℕ)

module Data.FOL.Deep.ATP.Metis (n : ℕ) where

open import Data.FOL.Deep.Syntax n
open import Data.FOL.Deep.Theorems n

open import Data.FOL.Deep.Semantics n

open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)
open import Data.Bool using (Bool ; if_then_else_ ; true ; false)
  renaming (_∧_ to _&&_ ; _∨_ to _||_)
open import Function using (_$_)

open import Relation.Nullary.Decidable
open import Data.Fin
open import Data.Fin.Properties

-- Inference Rules.

equal-f : Prop → Prop → Bool
equal-f (Var x) (Var y) = ⌊ x ≟ y ⌋
equal-f ⊥ ⊥ = true
equal-f ⊤ ⊤ = true
equal-f (¬ φ) (¬ ψ) = equal-f φ ψ
equal-f (φ₁ ∧ φ₂) (ψ₁ ∧ ψ₂) =
  ((equal-f φ₁ ψ₁) && (equal-f φ₂ ψ₂)) || ((equal-f φ₁ ψ₂) && (equal-f φ₂ ψ₁))
equal-f (φ₁ ∨ φ₂) (ψ₁ ∨ ψ₂) =
  ((equal-f φ₁ ψ₁) && (equal-f φ₂ ψ₂)) || ((equal-f φ₁ ψ₂) && (equal-f φ₂ ψ₁))
equal-f (φ₁ ⇒ φ₂) (ψ₁ ⇒ ψ₂) = (equal-f φ₁ ψ₁) && (equal-f φ₂ ψ₂)

equal-f φ ψ = false


$false : Prop
$false = ⊥

strip : Prop → Prop
strip (Var x) = (Var x)
strip (¬ ⊤) = ⊥
strip (¬ ⊥) = ⊤
strip (¬ φ) = ¬ φ
strip (φ₁ ∨ φ₂ ∨ φ₃) = (¬ φ₁) ∧ (¬ φ₂) ⇒ φ₃
strip (φ ∨ ψ) = (¬ φ) ⇒ ψ
strip (φ₁ ⇒ (φ₂ ⇒ φ₃)) = φ₁ ∧ (strip (φ₂ ⇒ φ₃))
strip φ = φ

atp-strip : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ strip φ
atp-strip {Γ} {Var x} = id
atp-strip {Γ} {(φ₁ ⇒ (φ₂ ⇒ φ₃))} =
  atp-step (λ _ → φ₁ ∧ strip (φ₂ ⇒ φ₃))
atp-strip {Γ} {¬ (φ ⇒ φ₁)} = id
atp-strip {Γ} {¬ ⊤} = ¬-⊤
atp-strip {Γ} {¬ ⊥} = ¬-⊥
atp-strip {Γ} {φ} seq = id (atp-step (λ _ → strip φ) seq)


atp-neg : Prop → Prop
atp-neg φ = ¬ φ

canonicalize : Prop → Prop
canonicalize (φ ⇒ ψ) = ¬ φ ∨ ψ
canonicalize (¬ (φ ⇒ ψ)) = φ ∧ ¬ ψ
canonicalize (¬ ⊤) = ⊥
canonicalize (¬ ⊥) = ⊤
canonicalize φ = φ

atp-canonicalize : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ canonicalize φ
atp-canonicalize {Γ} {Var x} = id
atp-canonicalize {Γ} {⊤} = id
atp-canonicalize {Γ} {⊥} = id
atp-canonicalize {Γ} {φ ∧ φ₁} = id
atp-canonicalize {Γ} {φ ∨ φ₁} = id
atp-canonicalize {Γ} {φ ⇒ φ₁} = impl-pos
atp-canonicalize {Γ} {¬ (φ ⇒ φ₁)} = impl-neg
atp-canonicalize {Γ} {¬ ⊤} = ¬-⊤
atp-canonicalize {Γ} {¬ ⊥} = ¬-⊥
atp-canonicalize {Γ} {φ} seq = id (atp-step (λ _ → canonicalize φ) seq)

simplify : Prop → Prop
simplify (φ ∧ ¬ ψ) = if (equal-f φ ψ) then ⊥ else (φ ∧ ¬ ψ)
simplify (¬ φ ∧ ψ) = if (equal-f φ ψ) then ⊥ else (¬ φ ∧ ψ)
simplify φ = φ


atp-simplify : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ simplify φ
atp-simplify {Γ} {Var x} = id
atp-simplify {Γ} {⊤} = id
atp-simplify {Γ} {⊥} = id
atp-simplify {Γ} {φ = φ₁ ∧ ¬ φ₂} seq =
  atp-step (λ _ → simplify (φ₁ ∧ ¬ φ₂)) seq
atp-simplify {Γ} {¬ φ ∧ ψ} =
  atp-step (λ _ → simplify (¬ φ ∧ ψ))
atp-simplify {Γ} {φ} seq = id (atp-step (λ _ → simplify φ) seq)


resolve : ∀ {Γ} {L C D} → Γ ⊢ L ∨ C → Γ ⊢ ¬ L ∨ D → Γ ⊢ C ∨ D
resolve {Γ} {L}{C}{D} seq₁ seq₂ =
  lem1 $ ⇒-elim {Γ = Γ}
    ∧-morgan₁
    (¬-intro {Γ = Γ} $
      ¬-elim {Γ = Γ , ¬ C ∧ ¬ D}
        (lem2 {Γ = Γ , ¬ C ∧ ¬ D} $
          ∧-intro
            (weaken (¬ C ∧ ¬ D) seq₂)
            (∧-proj₂ $ assume {Γ = Γ} $ ¬ C ∧ ¬ D))
        (lem2 $
           ∧-intro
            (weaken (¬ C ∧ ¬ D) seq₁)
             (∧-proj₁ $ assume {Γ = Γ} $ ¬ C ∧ ¬ D)))
