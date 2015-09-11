module Data.FOL.Base where

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

⊥-elim : { A : Set } → ⊥ → A
⊥-elim ()

infixl 5 _∧_ _∨_

data _∧_ ( A B : Set ) : Set where
  _,_ : A → B → A ∧ B

∧-proj₁ : ∀ {A B} → A ∧ B → A
∧-proj₁ (a , _) = a

∧-proj₂ : ∀ {A B} → A ∧ B → B
∧-proj₂ (_ , b) = b

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

case : ∀ {A B} → {C : Set} → (A → C) → (B → C) → A ∨ B → C
case f _ (inj₁ a) = f a
case _ g (inj₂ b) = g b

¬_ : Set → Set
¬ A = A → ⊥

postulate pem : ∀ {A} → A ∨ ¬ A
postulate D : Set

data ∃ ( A : D → Set ) : Set where
  _,_ : (t : D) → A t → ∃ A

∃-elim : { A : D → Set } {B : Set} → ∃ A → (∀ {x} → A x → B) → B
∃-elim (_ , Ax) h = h Ax

data _≡_ (x : D) : D → Set  where
  refl : x ≡ x

proofByContradiction : {Z : Set} → (¬ Z → ⊥) → Z
proofByContradiction {Z} contradiction = case' pem
  where
    case' : Z ∨ ¬ Z → Z
    case' (inj₁ z)  = z
    case' (inj₂ nz) = ⊥-elim (contradiction nz)
