open import Data.FOL.Deep 2 public

ex1 : ∀ {φ} → ∅ ⊢ φ ⇒ φ
ex1 {φ} = ⇒-intro (assume {Γ = ∅} φ)

ex2 : ∀ {φ ψ} → ∅ ⊢ (φ ∧ (φ ⇒ ψ)) ⇒ ψ
ex2 {φ} {ψ} =
  ⇒-intro
    (⇒-elim
      (∧-proj₂ (assume {Γ = ∅} (φ ∧ (φ ⇒ ψ))))
      (∧-proj₁ (assume {Γ = ∅}  (φ ∧ (φ ⇒ ψ)))))

ex3 : ∀ {φ ψ ω} → ∅ ⊢ (φ ∧ (ψ ∨ ω)) ⇒ ((φ ∧ ψ) ∨ (φ ∧ ω))
ex3 {φ} {ψ} {ω} =
  ⇒-intro
  (⇒-elim {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
    (⇒-intro {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
      (∨-elim {Γ = ∅ , (φ ∧ (ψ ∨ ω))}
        (∨-intro₁ {Γ = ∅ , (φ ∧ (ψ ∨ ω)) , ψ}
          (φ ∧ ω)
          (∧-intro
            (∧-proj₁ (weaken ψ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
            (assume {Γ = ∅ , (φ ∧ (ψ ∨ ω)) } ψ)))
        (∨-intro₂ {Γ = ∅ , (φ ∧ (ψ ∨ ω)) , ω}
          (φ ∧ ψ)
          (∧-intro
            (∧-proj₁ (weaken ω (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))
            (assume {Γ = ∅ , (φ ∧ (ψ ∨ ω))} ω )))))
    (∧-proj₂ (assume {Γ = ∅} (φ ∧ (ψ ∨ ω)))))

ex4 : ∀ {φ ψ} → ∅ ⊢ (¬ φ ∨ ψ) ⇒ (φ ⇒ ψ)
ex4 {φ} {ψ} =
  ⇒-intro $
    ∨-elim {Γ = ∅}
      (⇒-intro
        (⊥-elim ψ
          (¬-elim
            (weaken φ (assume {Γ = ∅} (¬ φ)))
            (assume {Γ = ∅ , ¬ φ} φ))))
      (⇒-intro (weaken φ (assume {Γ = ∅} ψ)))

