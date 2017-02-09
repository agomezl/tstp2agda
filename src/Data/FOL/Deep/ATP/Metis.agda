open import Data.Nat using (ℕ)

module Data.FOL.Deep.ATP.Metis (n : ℕ) where

open import Data.FOL.Deep.Syntax n
open import Data.FOL.Deep.Theorems n

open import Function using (_$_)

-- Inference Rules.


atp-strip : Prop → Prop
atp-strip φ = φ

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
