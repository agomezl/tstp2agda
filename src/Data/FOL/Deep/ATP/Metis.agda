open import Data.Nat public using (ℕ)

module Data.FOL.Deep.ATP.Metis (n : ℕ) where

open import Data.FOL.Deep.Syntax n
open import Data.FOL.Deep.Theorems n

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
