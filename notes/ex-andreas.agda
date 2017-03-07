open import Data.FOL.Deep 2 public


-- Vars
a : Prop
a = Var (# 0)

b : Prop
b = Var (# 1)

ex1 : ∀ {φ} → ∅ ⊢ φ ⇒ φ
ex1 {φ} = ⇒-intro (assume {Γ = ∅} φ)

ex2 : ∀ {φ ψ} → ∅ ⊢ (φ ∧ (φ ⇒ ψ)) ⇒ ψ
ex2 {φ} {ψ} = ⇒-intro (⇒-elim (∧-proj₂ (assume {Γ = ∅} (φ ∧ (φ ⇒ ψ)))) (∧-proj₁ (assume {Γ = ∅}  (φ ∧ (φ ⇒ ψ)))))

-- ex3 : ∀ {φ ψ ω} → ∅ ⊢ (φ ∧ (ψ ∨ ω)) ⇒ ((φ ∧ ψ) ∨ (φ ∧ ω))
-- ex3 {φ} {ψ} {ω} = ⇒-intro (⇒-elim (∨-elim {!∨-intro₂!} {!!}) (∧-proj₂ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
