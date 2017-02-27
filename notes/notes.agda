
remove2 : Prop → Prop → Prop
remove2 (a ∨ b) e with (equal-f b e)
... | true  = b ∨ a
... | false = a ∨ b
remove2 φ _ = φ

remove3 : Prop → Prop → Prop
remove3 φ@((a ∨ b) ∨ c) d with (equal-f c d)
... | true = c ∨ (a ∨ b)
... | false with (equal-f b d)
...          | true  = b ∨ (a ∨ c)
...          | false with (equal-f a d)
...                   | true  = a ∨ (b ∨ c)
...                   | false = φ
remove3 φ _ = φ

remove4 : Prop → Prop → Prop
remove4 φ@(((a ∨ b) ∨ c) ∨ d) e with (equal-f d e)
... | true  = d ∨ ((a ∨ b) ∨ c)
... | false with (equal-f c e)
...         | true  = c ∨ ((a ∨ b) ∨ d)
...         | false with (equal-f b e)
...                  | true  = b ∨ ((a ∨ c) ∨ d)
...                  | false with (equal-f a e)
...                           | true  = a ∨ ((b ∨ c) ∨ d)
...                           | false = φ
remove4 φ _ = φ

remove₀ : Prop → Prop → Prop
remove₀ φ@((((Var x) ∨ b) ∨ c) ∨ d) ψ = remove4 φ ψ
remove₀ φ@(((⊤ ∨ b) ∨ c) ∨ d) ψ = remove4 φ ψ
remove₀ φ@(((⊥ ∨ b) ∨ c) ∨ d) ψ = remove4 φ ψ
remove₀ φ@((((a ∧ a₁) ∨ b) ∨ c) ∨ d) ψ = remove4 φ ψ
remove₀ φ@((((a ⇒ a₁) ∨ b) ∨ c) ∨ d) ψ = remove4 φ ψ
remove₀ φ@((((a ⇔ a₁) ∨ b) ∨ c) ∨ d) ψ = remove4 φ ψ
remove₀ φ@(((¬ a ∨ b) ∨ c) ∨ d) ψ = remove4 φ ψ
--remove₀ (a ∨ a₁ ∨ b ∨ c ∨ d) ψ = remove4 ψ

remove₀ φ@(((Var x) ∨ b) ∨ c) ψ = remove3 φ ψ
remove₀ φ@((⊤ ∨ b) ∨ c) ψ = remove3 φ ψ
remove₀ φ@((⊥ ∨ b) ∨ c) ψ = remove3 φ ψ
remove₀ φ@(((a ∧ a₁) ∨ b) ∨ c) ψ = remove3 φ ψ
remove₀ φ@(((a ⇒ a₁) ∨ b) ∨ c) ψ = remove3 φ ψ
remove₀ φ@(((a ⇔ a₁) ∨ b) ∨ c) ψ = remove3 φ ψ
remove₀ φ@((¬ a ∨ b) ∨ c) ψ = remove3 φ ψ

--remove₀ (a ∨ a₁) ∨ b) ∨ c) ψ = remove3 φ ψ
remove₀ φ@((Var x) ∨ b) ψ = remove2 φ ψ
remove₀ φ@(⊤ ∨ b) ψ = remove2 φ ψ
remove₀ φ@(⊥ ∨ b) ψ = remove2 φ ψ
remove₀ φ@((a ∧ a₁) ∨ b) ψ = remove2 φ ψ
remove₀ φ@((a ⇒ a₁) ∨ b) ψ = remove2 φ ψ
remove₀ φ@((a ⇔ a₁) ∨ b) ψ = remove2 φ ψ
remove₀ φ@(¬ a ∨ b) ψ = remove2 φ ψ

remove₀ ((a ∨ b) ∨ c) ψ with (equal-f c ψ)
... | true = ∨-comm
remove₀ φ _ = φ

pick4-φ₁ : ∀ {Γ} {φ₁ φ₂ φ₃ φ₄} → Γ ⊢ (((φ₁ ∨ φ₂) ∨ φ₃) ∨ φ₄) → Γ ⊢ (φ₁ ∨ ((φ₂ ∨ φ₃) ∨ φ₄))
pick4-φ₁ {Γ} {φ₁}{φ₂}{φ₃}{φ₄} seq =
  ⇒-elim
  (⇒-intro
    (∨-elim {Γ = Γ}
      (∨-assoc₁
        (∨-intro₁
          φ₄
          (∨-assoc₁ (assume {Γ = Γ} ((φ₁ ∨ φ₂) ∨ φ₃)))))
          (∨-intro₂ φ₁ (∨-intro₂ (φ₂ ∨ φ₃) (assume {Γ = Γ} φ₄)))))
          seq

pick4-φ₂  : ∀ {Γ} {φ₁ φ₂ φ₃ φ₄} → Γ ⊢ (((φ₁ ∨ φ₂) ∨ φ₃) ∨ φ₄) → Γ ⊢ (φ₂ ∨ ((φ₁ ∨ φ₃) ∨ φ₄))
pick4-φ₂ {Γ} {φ₁}{φ₂}{φ₃}{φ₄} seq =
  ⇒-elim
  (⇒-intro
    (∨-elim {Γ = Γ}
      (∨-assoc₁
        (∨-intro₁
          φ₄
          (∨-pick (assume {Γ = Γ} ((φ₁ ∨ φ₂) ∨ φ₃)))))
          (∨-intro₂ φ₂ (∨-intro₂ (φ₁ ∨ φ₃) (assume {Γ = Γ} φ₄)))))
          seq

pick4-φ₃  : ∀ {Γ} {φ₁ φ₂ φ₃ φ₄} → Γ ⊢ (((φ₁ ∨ φ₂) ∨ φ₃) ∨ φ₄) → Γ ⊢ (φ₃ ∨ ((φ₁ ∨ φ₂) ∨ φ₄))
pick4-φ₃  = ∨-pick

pick4-φ₄  : ∀ {Γ} {φ₁ φ₂ φ₃ φ₄} → Γ ⊢ (((φ₁ ∨ φ₂) ∨ φ₃) ∨ φ₄) → Γ ⊢ (φ₄ ∨ ((φ₁ ∨ φ₂) ∨ φ₃))
pick4-φ₄  = ∨-comm

-- proof-remove₀ : ∀ {Γ} {φ} → (ψ : Prop) → Γ ⊢ φ → Γ ⊢ (remove₀ φ ψ)
-- proof-remove₀ {Γ} {(((φ₁@(Var _) ∨ φ₂) ∨ φ₃) ∨ φ₄)} ψ with (equal-f φ₄ ψ)
-- ... | true = ∨-comm
-- ... | false with (equal-f φ₃ ψ)
-- ...         | true = pick4-φ₃
-- ...         | false with (equal-f φ₂ ψ)
-- ...                 | true = pick4-φ₂
-- ...                 | false with (equal-f φ₁ ψ)
-- ...                         | true  = pick4-φ₁
-- ...                         | false = id
-- proof-remove₀ {Γ} {((φ₁@(Var _) ∨ φ₂) ∨ φ₃)} ψ with (equal-f φ₃ ψ)
-- ... | true = ∨-comm
-- ... | false with (equal-f φ₂ ψ)
-- ...         | true  = ∨-pick
-- ...         | false with (equal-f φ₁ ψ)
-- ...                 | true = ∨-assoc₁
-- ...                 | false = id
-- proof-remove₀ {Γ} {φ₁@(Var _) ∨ φ₂} ψ with (equal-f φ₂ ψ)
-- ... | true  = ∨-comm
-- ... | false = id
-- proof-remove₀ {Γ} {φ} ψ seq = id (atp-step (λ _ → remove₀ φ ψ) seq)
